#if you want to use a different port, then start like this:
# sh start 3666

#sh clean.sh #this deletes the database so every time we re-start, we have 0 blocks again. only needed during testing.
#compile the c code.

gcc -Ofast -march=native -fPIC -shared -o ebin/fq.so src/crypto/fq.c -I $ERL_ROOT/user/include/

gcc -Ofast -march=native -funroll-loops -fomit-frame-pointer -flto -fPIC -shared -o ebin/fq2.so src/crypto/fq2.c -I $ERL_ROOT/user/include/
#gcc -Ofast -march=native -fomit-frame-pointer -flto -fPIC -shared -o ebin/fq2.so src/crypto/fq2.c -I $ERL_ROOT/user/include/

./rebar get-deps
sh clean.sh #this deletes the database so every time we re-start, we have 0 blocks again. only needed during testing.
./rebar compile #this line checks if any modules were modified, and recompiles them if they were. only needed during testing.
mkdir data
erl -pa ebin deps/*/ebin/ -eval "application:ensure_all_started(trie)."

