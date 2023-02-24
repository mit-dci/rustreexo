PREFIX=/usr
OBJECT_INSTALL_PATH=${PREFIX}/lib
HEADERS_INSTALL_PATH=${PREFIX}/include
LIB_NAME=librustreexo
LIB_FILE_NAME=librustreexo.so
LICENSE_PATH=${PREFIX}/share/licenses
BUILD_PATH=$(PWD)/../target/release/
DEBUG_BUILD_PATH=$(PWD)/../target/debug/
LD_LIBRARY_PATH=$(DEBUG_BUILD_PATH)

# This compiler is used for building C artifacts, like examples and tests
CC=gcc

all: build

clean:
	cargo clean
	rm -rf $(PWD)/examples/simple_test

build:
	cargo build --release

tests: build-debug
	$(CC) -Wmissing-field-initializers -I $(PWD)/include/ -L $(PWD)/../target/debug/ $(PWD)/tests/run_testcases.c -l:$(LIB_FILE_NAME) -lcrypto -g -o $(PWD)/build/tests

build-debug:
	cargo build

examples: build-debug
	$(CC) -Wmissing-field-initializers -I $(PWD)/include/ -L $(PWD)/../target/debug/ examples/simple_stump_example.c -l:$(LIB_FILE_NAME) -lcrypto -g -o $(PWD)/build/simple_test
	$(CC) -Wmissing-field-initializers -I $(PWD)/include/ -L $(PWD)/../target/debug/ examples/proof_update.c -l:$(LIB_FILE_NAME) -lcrypto -g -o $(PWD)/build/proof_update
	$(CC) -Wmissing-field-initializers -I $(PWD)/include/ -L $(PWD)/../target/debug/ examples/proof_verify.c -l:$(LIB_FILE_NAME) -lcrypto -g -o $(PWD)/build/proof_verify

install: build
	sudo mkdir -p $(HEADERS_INSTALL_PATH)/$(LIB_NAME)/
	sudo cp $(PWD)/include/* $(HEADERS_INSTALL_PATH)/$(LIB_NAME)/
	sudo cp $(PWD)/../target/release/$(LIB_FILE_NAME) $(OBJECT_INSTALL_PATH)/$(LIB_FILE_NAME)
	sudo cp $(PWD)/../target/release/$(LIB_FILE_NAME) $(OBJECT_INSTALL_PATH)/$(LIB_NAME).a
	sudo mkdir -p $(LICENSE_PATH)/$(LIB_NAME)/
	sudo cp -r $(PWD)/../LICENSE $(LICENSE_PATH)/$(LIB_NAME)/LICENSE

uninstall:
	sudo rm -r $(HEADERS_INSTALL_PATH)/$(LIB_NAME)/
	sudo rm $(OBJECT_INSTALL_PATH)/$(LIB_FILE_NAME)

run-examples:
	LD_LIBRARY_PATH=$(LD_LIBRARY_PATH) $(PWD)/examples/simple_test
	LD_LIBRARY_PATH=$(LD_LIBRARY_PATH) $(PWD)/examples/proof_update