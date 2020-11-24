CHERI_MODEL_PATH = ../../l3mips
EXPORT_PATH      = $(CHERI_MODEL_PATH)/src/hol
EXPORT_FILE_NAME = CHERI_Monadic

default: update_source generate-p256 generate-c128concentrate

# If after updating the source "make" throws an error, this might be
# caused by an outdated version of L3.

update_l3:
	wget -O ~/l3.tar.bz2 http://www.cl.cam.ac.uk/~acjf3/l3/l3.tar.bz2
	cd ~ && tar -xjvf l3.tar.bz2
	rm ~/l3.tar.bz2
	echo "Run Make in the new directory and update PATH variable in .profile."

update_source:
	cd $(CHERI_MODEL_PATH) && git pull

generate-p256:
	cd $(CHERI_MODEL_PATH) && $(MAKE) clean && $(MAKE) isabelle_monadic CAP=p256
	cp $(EXPORT_PATH)/$(EXPORT_FILE_NAME).thy $(EXPORT_FILE_NAME)_p256.thy
	rm $(EXPORT_PATH)/$(EXPORT_FILE_NAME).thy
	sed -i 's/$(EXPORT_FILE_NAME)/$(EXPORT_FILE_NAME)_p256/g' $(EXPORT_FILE_NAME)_p256.thy

generate-c128concentrate:
	cd $(CHERI_MODEL_PATH) && $(MAKE) clean && $(MAKE) isabelle_monadic CAP=c128concentrate
	cp $(EXPORT_PATH)/$(EXPORT_FILE_NAME).thy $(EXPORT_FILE_NAME)_c128concentrate.thy
	rm $(EXPORT_PATH)/$(EXPORT_FILE_NAME).thy
	sed -i 's/$(EXPORT_FILE_NAME)/$(EXPORT_FILE_NAME)_c128concentrate/g' $(EXPORT_FILE_NAME)_c128concentrate.thy

build-p256:
	isabelle build -b -s CHERI-p256

build-c128concentrate:
	isabelle build -b -s CHERI-c128concentrate
