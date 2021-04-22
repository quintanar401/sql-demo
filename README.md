Rust:

`cargo run --release`

release is important because otherwise a 100mil long table take too long to generate

when > appears run

```sql
select sym,size,count(*),avg(price) into r from bt group by sym,size
select * from (select sym,size,count(*),avg(price) into r from bt where price>10.0 and sym='fb' group by sym,size) as t1 join ref on t1.sym=ref.sym, t1.size = ref.size

count(bt)
set var rand('i',1000)
set var rand('f',1000)
set var rand('s',1000)
set tbl [cname var]
1+2
1-2
1/2
1*2
1 or 2
1 and 2
not 1
1=2
1<>2
1>2
1<2

quit
```

fns: sum, avg, max, min, count.

Q:

`q demo.q -s 16`

```sql
sel "select sym,size,count(*),avg(price) into r from bt group by sym,size"
\t sel "select sym,size,count(*),avg(price) into r from bt group by sym,size"
```

and etc

`\t select count i, avg price by sym, size from qbt`

to compare with the native Q (free Q is 32bit and can't process 100mil, in Rust use bt2 which has 10mil rows)

to quit: `\\`