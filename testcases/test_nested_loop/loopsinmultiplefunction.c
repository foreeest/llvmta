int exec() {
	return 0;
}

int a() {
	for (int i = 0; i < 12; ++i) {
		exec();
	}
	return 1;
}

int b() {
	for (int i = 2; i < 5; ++i) {
		exec();
	}
	return 2;
}

int loopsinmultiplefunction_main() {
	a();
	b();
	return 0;
}
