/* run.config
   EXECNOW: make tests/aorai/Aorai_test.cmxs
   DONTRUN: small example related to U3CAT's WP2
*/
int x=0 ;
int y =0 ;
void f(void) { 
	x = 1;
	x = 0; 
}

void g(void) { x++; x--; }

int main() {

while(y < 5){
  if (!x) { f(); }
  y++;
  y = y + y;
  g();
}
  return 0;
}
