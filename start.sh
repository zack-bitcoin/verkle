#if you want to use a different port, then start like this:
# sh start 3666

#sh clean.sh #this deletes the database so every time we re-start, we have 0 blocks again. only needed during testing.
#compile the c code.

# Fast code version.
#gcc -Ofast -march=native -funroll-loops -fomit-frame-pointer -flto -fPIC -shared -o ebin/fq.so src/crypto/fq.c -I $ERL_ROOT/user/include/

# balanced version

gcc -O2 -march=native -funroll-loops -fomit-frame-pointer -flto -fPIC -shared -o ebin/fr.so src/crypto/fr.c -I $ERL_ROOT/user/include/

gcc -O2 -march=native -funroll-loops -fomit-frame-pointer -flto -fPIC -shared -o ebin/ed25519.so src/crypto/ed25519.c -I $ERL_ROOT/user/include/

# fast compile version
#gcc -fPIC -shared -o ebin/fq.so src/crypto/fq.c -I $ERL_ROOT/usr/include/
#gcc -fPIC -shared -o ebin/fr.so src/crypto/fr.c -I $ERL_ROOT/usr/include/

./rebar3 get-deps
#sh clean.sh #this deletes the database so every time we re-start, we have 0 blocks again. only needed during testing.
./rebar3 compile #this line checks if any modules were modified, and recompiles them if they were. only needed during testing.
#mkdir data
#erl -pa ebin deps/*/ebin/ -eval "application:ensure_all_started(verkle)."

#./rebar3 as prod release

#./_build/prod/rel/verkle/bin/verkle daemon

#erl -pa ebin deps/*/ebin/ -eval "application:start(verkle)"
mkdir data
erl -pa ebin ebin/* ebin _build/default/lib/*/ebin/ -eval "application:ensure_all_started(verkle)."
