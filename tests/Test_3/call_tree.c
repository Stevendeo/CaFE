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
