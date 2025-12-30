.PHONY: verify verify-core verify-docs verify-wip verify-changed doctor

verify:
	@scripts/verify_all.sh

verify-core:
	@RUN_MODE=core scripts/verify_all.sh

verify-docs:
	@RUN_MODE=docs scripts/verify_all.sh

verify-wip:
	@RUN_MODE=wip scripts/verify_all.sh

verify-changed:
	@scripts/verify_changed.sh

doctor:
	@scripts/doctor.sh
