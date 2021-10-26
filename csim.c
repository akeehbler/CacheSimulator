//Name: Alec Keehbler
// School: UW Madison
////////////////////////////////////////////////////////////////////////////////

/*
 * csim.c:  
 * A cache simulator that can replay traces (from Valgrind) and output
 * statistics for the number of hits, misses, and evictions.
 * The replacement policy is LRU.
 *
 * Implementation and assumptions:
 *  1. Each load/store can cause at most 1 cache miss plus a possible eviction.
 *  2. Instruction loads (I) are ignored.
 *  3. Data modify (M) is treated as a load followed by a store to the same
 *  address. Hence, an M operation can result in two cache hits, or a miss and a
 *  hit plus a possible eviction.
 */  

#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <string.h>
#include <errno.h>
#include <stdbool.h>

/******************************************************************************/
/* DO NOT MODIFY THESE VARIABLES **********************************************/

//Globals set by command line args.
int b = 0; //number of block (b) bits
int s = 0; //number of set (s) bits
int E = 0; //number of lines per set

//Globals derived from command line args.
int B; //block size in bytes: B = 2^b
int S; //number of sets: S = 2^s

//Global counters to track cache statistics in access_data().
int hit_cnt = 0;
int miss_cnt = 0;
int evict_cnt = 0;

//Global to control trace output
int verbosity = 0; //print trace if set
/******************************************************************************/
  
  
//Type mem_addr_t: Use when dealing with addresses or address masks.
typedef unsigned long long int mem_addr_t;

//Type cache_line_t: Use when dealing with cache lines.
typedef struct cache_line {                    
    char valid;
    mem_addr_t tag;
    //Data member for LRU tracking.
    long counter;
} cache_line_t;

//Type cache_set_t: Use when dealing with cache sets
//Note: Each set is a pointer to a heap array of one or more cache lines.
typedef cache_line_t* cache_set_t;
//Type cache_t: Use when dealing with the cache.
//Note: A cache is a pointer to a heap array of one or more sets.
typedef cache_set_t* cache_t;

// Create the cache (i.e., pointer var) we're simulating.
cache_t cache;  

/* 
 * init_cache:
 * Allocates the data structure for a cache with S sets and E lines per set.
 * Initializes all valid bits and tags with 0s.
 */                    
void init_cache() {
	//not sure if have to set B and S or if given
	//S = 2^s
	S = 2 << (s-1); 
	//B = 2^b
	B = 2 << (b-1);
	cache = malloc(S * sizeof(cache_set_t));
	//need error checking when using malloc
	if (cache == NULL){
	       	printf("Malloc did not allocate the number of Sets correctly");
       		exit(1);
   	 }	
	for(int i = 0; i < S; i++){
		cache[i] = malloc(E* sizeof(cache_line_t));
		if(cache[i] == NULL){
			printf("Malloc did not allocate the number of lines per Set correctly");
               		exit(1);
		}
		//initialize values in each line(j are the lines
		for(int j = 0; j < E; j++){
			cache[i][j].counter = 0;
			cache[i][j].valid = '0';
			cache[i][j].tag = 0;
		}
	}

}
  

/* 
 * free_cache:
 * Frees all heap allocated memory used by the cache.
 */                    
void free_cache() { 
	//free each of the sets in the cache
	for(int i = 0; i < S; i++){
		free(cache[i]);
		cache[i] = NULL;
	}
	//frees the cache
	free(cache);
	cache = NULL;	
}
   
   
/* 
 * access_data:
 * Simulates data access at given "addr" memory address in the cache.
 *
 * If already in cache, increment hit_cnt
 * If not in cache, cache it (set tag), increment miss_cnt
 * If a line is evicted, increment evict_cnt
 */                    
void access_data(mem_addr_t addr) {
	//need to shift by s and b to get to the tag since s and b are first
	mem_addr_t tag = addr >> (s+b);
	//must shift to get to the set that it is in
	mem_addr_t set = (addr - (tag << (s+b))) >> b;
	//initially the most recent and least recent are the same
	cache_line_t *mostrecent_line = &cache[set][0];
	cache_line_t *leastrecent_line = &cache[set][0];
	cache_line_t *empty_line = NULL;
	cache_line_t *hit_line = NULL;

	//loop through the lines
	for(int i = 0; i < E; i++){
		//Used for eviction: checks if there is an empty line in theset
		if(cache[set][i].valid == '0')
			empty_line = &cache[set][i];
		//valid
		else{
			//if find the matching tag - hit, so set pointer
			if(cache[set][i].tag == tag){
				hit_line = &cache[set][i];
			}
			//need to update the mostrecent line if it has a greater counter
			if(cache[set][i].counter > mostrecent_line->counter){
				mostrecent_line = &cache[set][i];
			}
			//need to update the leastrecent line if it has a smaller counter
			if(cache[set][i].counter < leastrecent_line->counter){
				leastrecent_line = &cache[set][i];
			}
		}
	}
	//a hit was found 
	if(hit_line != NULL){
		//update counter since it is now the mru
		hit_line->counter = mostrecent_line->counter + 1;
		hit_cnt++; 
	}
	//no eviction needed, since there is open space in the set
	else if(empty_line != NULL){
		//updates the newly placed data in the set, it is now valid
		empty_line-> valid = '1';
		empty_line->tag = tag;
		empty_line->counter = mostrecent_line->counter + 1;
		miss_cnt++;//it missed so must update count
	}
	//Eviction needed: not a hit or cold miss so it is a conflict miss
	else{
		//Class requiremnet: using the least recently used cache replacement policy
		leastrecent_line->valid = '1';
		leastrecent_line->tag = tag;
		leastrecent_line->counter = mostrecent_line-> counter + 1;
		//it was a miss and eviction needed so update both counters
		miss_cnt++;
		evict_cnt++;
	}
}
  
  
/* 
 * replay_trace:
 * Replays the given trace file against the cache.
 *
 * Reads the input trace file line by line.
 * Extracts the type of each memory access : L/S/M
 * TRANSLATE each "L" as a load i.e. 1 memory access
 * TRANSLATE each "S" as a store i.e. 1 memory access
 * TRANSLATE each "M" as a load followed by a store i.e. 2 memory accesses 
 */                    
void replay_trace(char* trace_fn) {           
    char buf[1000];  
    mem_addr_t addr = 0;
    unsigned int len = 0;
    FILE* trace_fp = fopen(trace_fn, "r"); 

    if (!trace_fp) { 
        fprintf(stderr, "%s: %s\n", trace_fn, strerror(errno));
        exit(1);   
    }

    while (fgets(buf, 1000, trace_fp) != NULL) {
        if (buf[1] == 'S' || buf[1] == 'L' || buf[1] == 'M') {
            sscanf(buf+3, "%llx,%u", &addr, &len);
      
            if (verbosity)
                printf("%c %llx,%u ", buf[1], addr, len);

            // GIVEN: 1. addr has the address to be accessed
            //        2. buf[1] has type of acccess(S/L/M)
            // call access_data function here depending on type of access
	if(buf[1] == 'M') //does it twice, since load followed by a store;
		access_data(addr);
	access_data(addr);
            if (verbosity)
                printf("\n");
        }
    }

    fclose(trace_fp);
}  
  
  
/*
 * print_usage:
 * Print information on how to use csim to standard output.
 */                    
void print_usage(char* argv[]) {                 
    printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of s bits for set index.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of b bits for block offsets.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
    exit(0);
}  
  
  
/*
 * print_summary:
 * Prints a summary of the cache simulation statistics to a file.
 */                    
void print_summary(int hits, int misses, int evictions) {                
    printf("hits:%d misses:%d evictions:%d\n", hits, misses, evictions);
    FILE* output_fp = fopen(".csim_results", "w");
    assert(output_fp);
    fprintf(output_fp, "%d %d %d\n", hits, misses, evictions);
    fclose(output_fp);
}  
  
  
/*
 * main:
 * Main parses command line args, makes the cache, replays the memory accesses
 * free the cache and print the summary statistics.  
 */                    
int main(int argc, char* argv[]) {                      
    char* trace_file = NULL;
    char c;
    
    // Parse the command line arguments: -h, -v, -s, -E, -b, -t 
    while ((c = getopt(argc, argv, "s:E:b:t:vh")) != -1) {
        switch (c) {
            case 'b':
                b = atoi(optarg);
                break;
            case 'E':
                E = atoi(optarg);
                break;
            case 'h':
                print_usage(argv);
                exit(0);
            case 's':
                s = atoi(optarg);
                break;
            case 't':
                trace_file = optarg;
                break;
            case 'v':
                verbosity = 1;
                break;
            default:
                print_usage(argv);
                exit(1);
        }
    }

    //Make sure that all required command line args were specified.
    if (s == 0 || E == 0 || b == 0 || trace_file == NULL) {
        printf("%s: Missing required command line argument\n", argv[0]);
        print_usage(argv);
        exit(1);
    }

    //Initialize cache.
    init_cache();

    //Replay the memory access trace.
    replay_trace(trace_file);

    //Free memory allocated for cache.
    free_cache();

    //Print the statistics to a file.
    //DO NOT REMOVE: This function must be called for test_csim to work.
    print_summary(hit_cnt, miss_cnt, evict_cnt);
    return 0;   
}  
