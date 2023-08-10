// A linked list starting from 'a' is created. Since the loop is not determined, a can be an alias to b,c,d,e or f
class P1{
	int val;
	P1 next;
}

class List{
	void listMaker(){
		P1 a,b,c,d,e,f;
		a = new P1();
		b = new P1();
		a.next = b;
		c = new P1();
		b.next = c;
		d = new P1();
		c.next = d;
		e = new P1();
		d.next = e;
		f = new P1();
		e.next = f;
		
		boolean flag = false;
		while(flag){
			a = a.next;
		}
	}
	
}

