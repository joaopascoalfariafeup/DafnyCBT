
publish/DafnyCBT test/correct_progs/in/ -o test/correct_progs/out/ >& test/correct_progs_log.txt & 

publish/DafnyCBT test/buggy_progs/in/ -o test/buggy_progs/out/ >& test/buggy_progs_log.txt & 

publish/DafnyCBT test/stuck/in/ -o test/stuck/out/ >& test/stuck_log.txt & 

publish/DafnyCBT test/verifixer/original/ -o test/verifixer/original_out/ >& test/verifixer_original_log.txt & 

publish/DafnyCBT test/verifixer/killed/ -o test/verifixer/killed_out/ >& test/verifixer_killed_log.txt &

publish/DafnyCBT test/verifixer/not_supported/ -o test/verifixer/not_supported_out/ >& test/verifixer_not_supported_log.txt &

publish/DafnyCBT test/has_errors/in/ -o test/has_errors/out/ --skip-on-exception --comment-uncompilable --grouping by-status -n 10 >& test/has_errors_log.txt &
