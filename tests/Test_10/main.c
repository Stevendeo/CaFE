void foo (int *tab, int length) {
	int i = 0;
	for (i;i<length; i++){
		tab[i] = i%4;

	}
	return;
}

int main(){

int x[5];

foo (x,5);

return 0;
}
