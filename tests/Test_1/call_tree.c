int x = -2;
void f(void) { 
	x ++;
	x --; 
	}

void g(void) {
	x ++;
	f();
	x --;

}
int main() {
  int i = 0;
  while(i < 10){
    i++;
    if(!x) f();
    g();
  }
  return 0;
}

