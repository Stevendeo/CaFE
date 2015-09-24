/* run.config
   EXECNOW: make tests/aorai/Aorai_test.cmxs
   DONTRUN: small example related to U3CAT's WP2
*/

int f(int s) { 
	return s ++;
	
}

int g(int s) {
	s = 1;
	s = 0;

	return s;

}

int main() {
  int x = 0;
  while(1){
    if(!x) x = f(x);
    x = g(x);
  } 
 return 0;

}
