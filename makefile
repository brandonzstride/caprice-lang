.PHONY: test
test:
	dune test --no-buffer
clean:
	dune clean