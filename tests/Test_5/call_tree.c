/* run.config
   EXECNOW: make tests/aorai/Aorai_test.cmxs
   DONTRUN: small example related to U3CAT's WP2
*/
int x=0 ;

void f(void) { 
	x ++;
	x --; 
}

void g(void) {
	x = 1;
	x = 0;

}

int main() {

while(1){

if(!x) f();
g();
}
  return 0;
}
