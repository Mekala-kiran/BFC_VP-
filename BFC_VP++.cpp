#define _CRT_SECURE_NO_WARNINGS
#include <iostream>
#include <string>
#include <cstdlib>
#include <algorithm>
#include <cstring>
#include <time.h>
#include <cstdio>
#include <cassert>
#include <cstdio>
#include <stdio.h>
#include <numeric>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <sstream>
#include <chrono>
#include <boost/random/mersenne_twister.hpp>
#include <boost/random/uniform_int_distribution.hpp>
#include <boost/random/uniform_real_distribution.hpp>
#include <boost/random/random_device.hpp>
#include <boost/variant.hpp>

using namespace std;
using namespace boost::random;

#define SZ(x) ((int)x.size())
#define ll long long
#define ull unsigned long long
#define ld long double
#define eps 1e-11
#define max(x,y) ((x)>(y)?(x):(y))
#define min(x,y) ((x)<(y)?(x):(y))

const int ITER_VER = 2200;
const ll shift = 1000 * 1000 * 1000LL;
const double TIME_LIMIT = 20;
const int N_WEDGE_ITERATIONS = 2 * 1000 * 1000 * 10;
const int ITERATIONS_SAMPLING = 5;
const int N_SPARSIFICATION_ITERATIONS = 5;
const int TIME_LIMIT_SPARSIFICATION = 10000; // !half an hour
const int N_FAST_EDGE_BFC_ITERATIONS = 2100; // used for fast edge sampling
const int N_FAST_WEDGE_ITERATIONS = 50; // used for fast wedge sampling

char output_address [2000] ;
char *input_address;


set <vector<int>> edges;
map<pair<int,int>,int> edge_sign,new_edge_sign; 
vector < pair <int, int>> list_of_edges;
map < int, int > vertices [2];
vector <int> index_map;
vector <int> vertices_in_left;
vector <int> vertices_in_right;
vector < vector <int> > adj,newadj;
vector < vector < int > > sampled_adj_list;
vector <bool> visited;
vector <int> list_of_vertices;
vector <int> vertex_counter;


ll count_wedge;
ll n_vertices;
ll n_edges;
ld exact_n_bf;
ld exact_n_bf_signed;
ld exact_n_bf_unsigned;
ll n_wedge_in_partition[2];
ll largest_index_in_partition[2];

vector <int> clr;
vector <int> hashmap_C;
vector <ll> sum_wedges;
vector <ll> sum_deg_neighbors;
vector <int> aux_array_two_neighboorhood;

void clear_everything() {
	largest_index_in_partition[0] = largest_index_in_partition[1] = 0;
	n_vertices = 0;
	n_edges = 0;
	edges.clear();
	vertices[0].clear(); vertices[1].clear();
	index_map.clear();
	vertices_in_left.clear();
	vertices_in_right.clear();
	adj.clear();
	sampled_adj_list.clear();
	visited.clear();
	//list_of_edges.clear();
	vertex_counter.clear();
	clr.clear();
	hashmap_C.clear();
	sum_wedges.clear();
	sum_deg_neighbors.clear();
	aux_array_two_neighboorhood.clear();
}

void resize_all() {
	clr.resize(n_vertices);
	hashmap_C.resize(n_vertices);
	aux_array_two_neighboorhood.resize(n_vertices);
	sum_wedges.resize(n_vertices);
	visited.resize(n_vertices);
	index_map.resize(n_vertices);
	sum_deg_neighbors.resize(n_vertices);
}



void add_vertex(int A, int side) {
	if (vertices[side].find(A) == vertices[side].end()) {
		if (side == 0) vertices_in_left.push_back(A);
		else vertices_in_right.push_back(A);
		vertices[side][A] = 1;
	}
}

void add_edge(int &A, int &B, int &sign) {
	add_vertex(A, 0);
	add_vertex(B, 1);

	if (edges.find({A,B,sign}) == edges.end()) {
		edges.insert({A,B,sign});

		n_edges++;
	}
}

void get_index(int &A, int side) {
	if (vertices[side].find(A) == vertices[side].end()) {
		vertices[side][A] = largest_index_in_partition[side] ++ ;
		/*print A and vertices[side][A] to get the generated id for the vertex A*/
		
		
		//cout<<"i am A"<<'\t'<<A<<'\n';
		// cout<< A << " " << side << " " << vertices[side][A]<<'\n';		
	}
	A = vertices[side][A];
}

bool all_num(string &s) {
	for (int i = 0; i < SZ(s); i++) if ((s[i] >= '0' && s [i] <= '9') == false) return false;
	return true;
}

void get_graph() {
	freopen(input_address, "r", stdin); //tries to open a file with a file stream that is associated with another opened file.
	printf("[%d:] File Opened\n", __LINE__);
	string s;
	cin.clear(); //clears the error flag on cin 
	while (getline(cin, s)) { //to read a string or a line from an input stream
 		stringstream ss; ss << s; //A stringstream associates a string object with a stream allowing you to read from the string as if it were a stream (like cin). To use stringstream, we need to include sstream header file.
 		
		vector <string> vec_str; 
		for (string z; ss >> z; vec_str.push_back(z));//push elements into a vector from the back
		if (SZ(vec_str) >= 2) {
			bool is_all_num = true;
			for (int i = 0; i < min (2, SZ(vec_str)) ; i++) is_all_num &= all_num(vec_str[i]);
			if (is_all_num) {
				int A, B, sign;
				ss.clear(); ss << vec_str[0]; ss >> A;
				ss.clear(); ss << vec_str[1]; ss >> B;
                ss.clear(); ss << vec_str[2]; ss >> sign;
				add_edge(A, B, sign);
				
			}
		}
	}
	printf("[%d:] File Reading Done!\n", __LINE__);
	vertices[0].clear();
	vertices[1].clear();
	largest_index_in_partition[0] = 0;
	largest_index_in_partition[1] = SZ(vertices_in_left);
	n_vertices = SZ(vertices_in_left) + SZ(vertices_in_right);
	adj.resize(n_vertices, vector <int> ());
	for (auto edge : edges) {
		int A = edge[0];  
		int B = edge[1];
        	int sign = edge[2];
		get_index(A, 0);
		get_index(B, 1);
		adj[A].push_back(B);
		adj[B].push_back(A);
        //list_of_edges.push_back(make_pair(A, B)); 
        edge_sign[{A, B}] = sign;
		edge_sign[{B, A}] = sign;
		
		
	}
	resize_all();

	n_wedge_in_partition[0] = 0;
	for (int i = 0; i < largest_index_in_partition[0]; i++) {
		n_wedge_in_partition[0] += (((ll)SZ(adj[i])) * (SZ(adj[i]) - 1)) >> 1;
	}
	n_wedge_in_partition[1] = 0;
	for (int i = largest_index_in_partition[0]; i < largest_index_in_partition[1]; i++) {
		n_wedge_in_partition[1] += ((ll)SZ(adj[i]) * (SZ(adj[i]) - 1)) >> 1;
	}
	for (int i = 0; i < n_vertices; i++) {
		sort(adj[i].begin(), adj[i].end());
		sum_deg_neighbors[i] = 0;
		for (auto neighbor : adj[i]) {
			sum_deg_neighbors[i] += SZ(adj[neighbor]);
		}
	}
	//cerr << " for test # edges :: " << SZ(list_of_edges) << " left :: " << SZ(vertices_in_left) << " right :: "  << SZ(vertices_in_right) << endl;
	//sort(list_of_edges.begin(), list_of_edges.end());
	edges.clear();
	fclose(stdin);
}

/*This function returns 1 if priority(u) < priority(v), otherwise it returns 0*/
//int priority(int u, int v){
//}

void read_the_graph(char *fin) {
	clear_everything();
	//cerr << " Insert the input (bipartite network) file location" << endl;
	//cerr << " >>> "; 
	input_address = fin;
	//cerr << " Insert the output file" << endl;
	//cerr << " >>> "; cin >> output_address;
	//freopen(output_address, "w", stdout);
	cerr << " ---------------------------------------------------------------------------------------------------------------------- \n";
	cerr << "| * Note that edges should be separated line by line.\n\
| In each line, the first integer number is considered as a vertex in the left partition of bipartite network, \n\
| and the second integer number is a vertex in the right partition. \n\
| In addition, multiple edges are removed from the given bipartite network.\n\
| Also, note that in this version of the source code, we did NOT remove vertices with degree zero.\n";
	cerr << " ---------------------------------------------------------------------------------------------------------------------- \n";

	cerr << " Processing the graph ... (please wait) \n";

	get_graph();   //function() from 27th line

	cout << " -------------------------------------------------------------------------- \n";
	cout << "Input graph: " << input_address << "\n";
	cout << " The graph is processed - there are " << n_vertices << " vertices and " << n_edges << " edges  \n";
	cout << " -------------------------------------------------------------------------- \n";
}
void projection(vector<vector<int>> adj)
{
	map<int,int> degree_left,degree_right;
	set<int> left,right;
	int min_index=INT_MAX;
	
	
	/*   cout<<"new adj list here"<<endl;
        // Print the contents of adj
    cout << "Contents of adj list:" << endl;
    for (int i = 0; i < adj.size(); ++i) {
        cout << "Vertex " << i << ": ";
       for (int j = 0; j < adj[i].size(); ++j) {
            cout << adj[i][j] << " ";
        }
        cout << endl;
   }*/
	
	
	map<int, vector<int>> verticesMap;
        vector<int>vertex_left;
        vector<int>vertex_right;
    // Iterate through the adjacency list and populate the map
   for (int i = 0; i < adj.size(); ++i) {
        int flag = 0;
   	
   	for(int j=0;j<adj[i].size();j++)
   	{
        	if(i < adj[i][j])
        	  flag++;
        }
        if(flag == adj[i].size())
           vertex_left.push_back(i);
        else
           vertex_right.push_back(i);            	  
       } 	
        	
      /*cout << "Vertices on the left side: ";
      for(int i=0;i<vertex_left.size();i++)
         cout<<vertex_left[i]<<" ";  	
         
      cout << "Vertices on the right side: ";
      for(int i=0;i<vertex_right.size();i++)
         cout<<vertex_right[i]<<" ";  	   
        	/*if (i < vertices_in_left.size()) {
            		verticesMap[vertices_in_left[i]] = adj[i];
       		 } else
            	verticesMap[vertices_in_right[i]] = adj[i];
            	*/
        //}
    //}
    
    	// Display the vertices on the left side
    /*cout << "Vertices on the left side: ";
    for (const auto& entry : verticesMap) {
        if (find(vertices_in_left.begin(), vertices_in_left.end(), entry.first) != vertices_in_left.end()) {
            cout << entry.first << " ";
        }
    }
    cout << endl;

    // Display the vertices on the right side
    cout << "Vertices on the right side: ";
    for (const auto& entry : verticesMap) {
        if (find(vertices_in_right.begin(), vertices_in_right.end(), entry.first) != vertices_in_right.end()) {
            cout << entry.first << " ";
        }
    }*/
    
    
    
    
    
	for(auto i:vertex_left) 
		min_index=min(min_index,i);
		
	for(auto i:vertex_right) 
		min_index=min(min_index,i);
		
	vector<pair<int,int>> pr_left,pr_right;
		
	//adjusting the values by subtracting min_index	
	for(auto i:vertex_left)
	{
	   left.insert(i-min_index);
        }    
	for(auto i:vertex_right)
	{
	    right.insert(i-min_index);
         }
	
	//finding degree for both sides
	for(int i=0;i<adj.size();i++)
	{
		for(int j=0;j<adj[i].size();j++)
		{

			if(left.find(i)!=left.end())
				degree_left[i]++;
			else degree_right[i]++;
		}
		
	}
	
	
	/*std::cout << "Degrees on the Left Side:" << std::endl;
	for (const auto &vertex : left) {
    std::cout << "Vertex " << vertex << ": " << degree_left[vertex] << std::endl;
}

std::cout << "Degrees on the Right Side:" << std::endl;
for (const auto &vertex : right) {
    std::cout << "Vertex " << vertex << ": " << degree_right[vertex] << std::endl;
}
		
	std::cout << "Elements in 'left' set: ";
        for (const auto &elem : left) {
         	std::cout << elem << " ";
        }
    	std::cout << std::endl;*/

    
	for(auto i:left)
	{
		if(degree_left.find(i)!=degree_left.end())
		 	pr_left.push_back({degree_left[i],i});
		else 
			pr_left.push_back({0,i});
	}
	
	/*std::cout << "Elements in 'right' set: ";
        for (const auto &elem : right) {
        	std::cout << elem << " ";
    	}
         std::cout << std::endl;*/
         
         
	for(auto i:right)
	{
		if(degree_right.find(i)!=degree_right.end())
		 	pr_right.push_back({degree_right[i],i});
		else 
			pr_right.push_back({0,i});
	}
	
	sort(pr_left.begin(),pr_left.end());
	sort(pr_right.begin(),pr_right.end());
	reverse(pr_left.begin(),pr_left.end());
	reverse(pr_right.begin(),pr_right.end());
	
		/*cout<<"left pr"<<endl;
		for(auto i:pr_left)
		{
			cout<<i.second<<" "<<i.first<<endl;
		}
		
		cout<<"right pr"<<endl;
		for(auto i:pr_right)
		{
			cout<<i.second<<" "<<i.first<<endl;
		}*/
							
		int lc=0,rc=0;
		map<int,int> ranking;
		for(int i=0;i<pr_right.size();i++)
		{
		ranking[pr_right[i].second]=lc;
		lc++;
		}
		for(int i=0;i<pr_left.size();i++)
		{
		ranking[pr_left[i].second]=lc;
		lc++;
		}
		//for(auto i:ranking) cout<<i.first<<" "<<i.second<<endl;
		//vector<vector<int>> newadj(n_vertices);
		newadj.resize(lc+1, vector <int> ());
		for(int i=0;i<adj.size();i++)
		{
		for(int j=0;j<adj[i].size();j++)
		{

		newadj[ranking[i]].push_back(ranking[adj[i][j]]);
		
		}
		}
		/*cout<<"new adj list here"<<endl;
	
	
		for(int i=0;i<newadj.size();i++)
		{
		cout<<i<<endl;
		for(auto j:newadj[i])
		{
		cout<<j<<" ";
		}
		cout<<endl;
		}*/
		for(int i=0;i<adj.size();i++)
		{
		
		for(int j=0;j<adj[i].size();j++)
		{
			new_edge_sign[{ranking[i],ranking[adj[i][j]]}]=edge_sign[{i,adj[i][j]}];
			}
		}
		//return newadj;
}

ll all_butterfly_counting(vector < vector <int> > &graph) {
ll res=0;
ll even_sign_res=0;
ll odd_sign_res=0;
	for(int u=0; u < n_vertices; u++){
		unordered_map<int, int> count_wedge;
		//cout<<"u "<<u<<endl;
        unordered_map<int, int> count_wedge_with_signs_0; // map for storing wedges(for particular u) who sign sum is 0 and the key of the map will be w vertex.
		unordered_map<int, int> count_wedge_with_signs_1; // map for storing wedges(for particular u) who sign sum is 1 and the key of the map will be w vertex.
		unordered_map<int, int> count_wedge_with_signs_2; // map for storing wedges(for particular u) who sign sum is 2 and the key of the map will be w vertex.
		set<int> n_w;
		for(int j = 0; j < SZ(graph[u]); j++)
		{
			int v = graph[u][j];
			//cout<<"v"<<v<<endl;
			if(SZ(graph[v]) < SZ(graph[u]) || ((SZ(graph[v]) == SZ(graph[u])) &&(v<u))){
				//int sign_sum = edge_sign[{u,v}]; // storing sign of the edge uv
				//int temp = sign_sum; // to store a copy of edge uv

				for(int k=0; k < SZ(graph[v]); k++){
					int w = graph[v][k];
					// cout<<"w"<<w<<endl;
					//sign_sum = temp; // renew the sign_sum
					 
					if(SZ(graph[w]) < SZ(graph[u]) ||  ((SZ(graph[w]) == SZ(graph[u])) &&(w<u))) {
						//printf("%d%d%d",u \t,v \t,w);
						//cout<<"this is u"<<'\t'<<u<<'\n'<<"this is v"<<'\t'<<v<<'\n'<<"this is w"<<'\t'<<w<<'\n'<<'\n';
						//cout<<"this is only u"<<u<<'\n';
                        //out << "u is " << u << " v is " << v << " w is " << w << " and sign sum is " <<  sign_sum << endl;

						//sign_sum += edge_sign[{v,w}]; // adding sign of vw to uv

						count_wedge[w] += 1;

					}
				}
			}
		}
	
	
		for(auto element : count_wedge)
		{
			if(element.second > 1){
			
				int val = element.second;
				res += val*(val-1)/2;
			}


		}

	}

	return res;
}

ll balanced_butterfly_counting_bucketing(vector < vector <int> > &graph) {
	ll res=0;
	ll balanced_bf_count=0;

	for(int u=0; u < n_vertices; u++){
        unordered_map<int, int> count_wedge_with_signs_0; // map for storing wedges(for particular u) who sign sum is 0 and the key of the map will be w vertex.
		unordered_map<int, int> count_wedge_with_signs_1; // map for storing wedges(for particular u) who sign sum is 1 and the key of the map will be w vertex.
		unordered_map<int, int> count_wedge_with_signs_2; // map for storing wedges(for particular u) who sign sum is 2 and the key of the map will be w vertex.
		set<int> n_w;
		for(int j = 0; j < SZ(graph[u]); j++)
		{
			int v = graph[u][j];
			
			if(SZ(graph[v]) < SZ(graph[u]) || ((SZ(graph[v]) == SZ(graph[u])) &&(v<u))){
				int sign_sum = new_edge_sign[{u,v}]; // storing sign of the edge uv
				int temp = sign_sum; // to store a copy of edge uv

				for(int k=0; k < SZ(graph[v]); k++){
					int w = graph[v][k];
					sign_sum = temp; // renew the sign_sum
					 
					if(SZ(graph[w]) < SZ(graph[u]) ||  ((SZ(graph[w]) == SZ(graph[u])) &&(w<u))) {
						//printf("%d%d%d",u \t,v \t,w);
						//cout<<"this is u"<<'\t'<<u<<'\n'<<"this is v"<<'\t'<<v<<'\n'<<"this is w"<<'\t'<<w<<'\n'<<'\n';
						//cout<<"this is only u"<<u<<'\n';
                        //out << "u is " << u << " v is " << v << " w is " << w << " and sign sum is " <<  sign_sum << endl;

						sign_sum += new_edge_sign[{v,w}]; // adding sign of vw to uv

						//count_wedge[w] += 1;

						//cout << "Sign sum is " << sign_sum << endl;

						n_w.insert(w); 
                        if(sign_sum == 0) {count_wedge_with_signs_0[w] +=1;}
                        else if(sign_sum == 1) {count_wedge_with_signs_1[w] +=1;}
                        else if(sign_sum == 2) {count_wedge_with_signs_2[w] +=1;}

					}
				}
			}
		}
	
	
        for(auto i : n_w)
		{
            int two_zeros = count_wedge_with_signs_0[i];//- -
            int one_zero = count_wedge_with_signs_1[i];// - +
            int two_ones = count_wedge_with_signs_2[i];// + +
			
			//cout << two_zeros << " " << one_zero << " " << two_ones << " " << u << " "<< i << endl;

			if((two_zeros+two_ones)>1)
            			balanced_bf_count += (((two_zeros+two_ones) * (two_zeros+two_ones -1)) / 2);
			if( (one_zero)>1)
				balanced_bf_count +=  (((one_zero) * (one_zero -1)) / 2);

			//cout << even_sign_res << " " << odd_sign_res << endl;
		}

	}
	return balanced_bf_count;
}
ll balanced_butterfly_counting_baseline(vector < vector <int> > &graph) {

	ll balanced_bf_count=0;
	for(int u=0; u < n_vertices; u++){
		set<int> n_w;
		unordered_map<int,vector<int>> wedges;
		for(int j = 0; j < SZ(graph[u]); j++)
		{
			int v = graph[u][j];
			
			if(SZ(graph[v]) < SZ(graph[u]) || ((SZ(graph[v]) == SZ(graph[u])) &&(v<u))){

				for(int k=0; k < SZ(graph[v]); k++){
					int w = graph[v][k];
					 
					if(SZ(graph[w]) < SZ(graph[u]) ||  ((SZ(graph[w]) == SZ(graph[u])) &&(w<u))) {
						//printf("%d%d%d",u \t,v \t,w);
						//cout<<"this is u"<<'\t'<<u<<'\n'<<"this is v"<<'\t'<<v<<'\n'<<"this is w"<<'\t'<<w<<'\n'<<'\n';
						//cout<<"this is only u"<<u<<'\n';
                        //out << "u is " << u << " v is " << v << " w is " << w << " and sign sum is " <<  sign_sum << endl;

						//cout << "Sign sum is " << sign_sum << endl;
						
						
						wedges[w].push_back(v);

						n_w.insert(w); 
					}
				}
			}
		}
		
		for(auto i : n_w){
			vector<int> vs = wedges[i];
			ll u1 = u;
			ll w1 = i;
			for(int j=0; j < vs.size()-1; j++){
				ll v1 = vs[j];

				for(int k=j+1; k < vs.size();k++){
					ll x1 = vs[k];
					int sign_sum1 = new_edge_sign[{u1,x1}] + new_edge_sign[{w1,x1}] +new_edge_sign[{u1,v1}] + new_edge_sign[{w1,v1}];
					if(sign_sum1 == 0 || sign_sum1 == 2 || sign_sum1 == 4) balanced_bf_count++;
				}
				

			}
		}
        
	}

	return balanced_bf_count;
}
		
		


void exact_algorithm_time_tracker(){


 /*for(int i=0;i<adj.size();i++)
		{
		cout<<"vertices "<<i<<":";
		for(auto j:adj[i])
		{
		cout<<j<<" ";
		}
		
		cout<<endl;
		
}*/


		
	std::chrono::_V2::system_clock::time_point t_start, t_end;
	t_start = std::chrono::high_resolution_clock::now();	
    	projection(adj);
    	ll total_butterfly_count = all_butterfly_counting(newadj); 
	t_end = std::chrono::high_resolution_clock::now();	
	double elapsed_time_all_butterfly = std::chrono::duration<double, std::milli>(t_end - t_start).count();
	
	printf("Total number of butterflies: %lld \t time taken: %f sec.\n", total_butterfly_count, elapsed_time_all_butterfly/1000);
	
	t_start = std::chrono::high_resolution_clock::now();	
    	ll balanced_butterfly_count_bucketing = balanced_butterfly_counting_bucketing(newadj); 
	t_end = std::chrono::high_resolution_clock::now();	
	double elapsed_time_bal_butterfly_bucketing = std::chrono::duration<double, std::milli>(t_end - t_start).count();

	printf("Total number of balanced butterflies: %lld \t Bucketing time taken: %f sec.\n",balanced_butterfly_count_bucketing , elapsed_time_bal_butterfly_bucketing/1000);
	
	t_start = std::chrono::high_resolution_clock::now();	
    	ll balanced_butterfly_count_baseline = balanced_butterfly_counting_baseline(newadj); 
	t_end = std::chrono::high_resolution_clock::now();	
	double elapsed_time_bal_butterfly_baseline = std::chrono::duration<double, std::milli>(t_end - t_start).count();
	
	printf("Total number of balanced butterflies: %lld \t Baseline time taken: %f sec.\n",balanced_butterfly_count_baseline , elapsed_time_bal_butterfly_baseline/1000);
	

	//cout << " Exact algorithm is done in " << elapsed_time << " secs. There are " << exact_n_bf << " total butterflies and " << "there are exactly " << exact_n_bf_signed << " number of signed butterflies." << endl;
}


int main(int argc, char *argv[])
{
	std::ios::sync_with_stdio(false);
	read_the_graph(argv[1]);
	exact_algorithm_time_tracker();
}


