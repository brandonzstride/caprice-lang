.PHONY: test
test:
	dune test --no-buffer --force
clean:
	dune clean