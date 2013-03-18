for nn in 03 06 10 13 19 20
do
    cat CO4/Test/Loop.hs \
	| sed -e "s/g03 d/g$nn d/" \
	> Loop-$nn.hs
    co4 -v Loop-$nn.hs > Loop-$nn.out &
done
