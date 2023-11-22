# This script prepares the following files:
# * YYYY-MM-DD-declaration_types.gz
# * YYYY-MM-DD-premises.gz
# * YYYY-MM-DD-export_infotree_full.tgz
# * YYYY-MM-DD-export_infotree_min.tgz
# * YYYY-MM-DD-training_data.tgz
# * YYYY-MM-DD-proof_step.tgz

DATE=`date "+%Y-%m-%d"`
mkdir -p out

lake build

lake exe declaration_types > out/$DATE-declaration_types
gzip -f out/$DATE-declaration_types

lake exe premises > out/$DATE-premises
gzip -f out/$DATE-premises

rm -rf out/export_infotree
./scripts/export_infotree.sh
cd out
tar cvzf $DATE-export_infotree_full.tgz export_infotree
cd ..
rm -rf out/export_infotree
./scripts/export_infotree.sh --tactics --original --substantive
cd out
tar cvzf $DATE-export_infotree_min.tgz export_infotree
cd ..

rm -rf out/training_data
./scripts/training_data.sh
cd out
tar cvzf $DATE-training_data.tgz training_data
cd ..
rm -rf out/training_data
./scripts/training_data.sh --proofstep
cd out
tar cvzf $DATE-proof_step.tgz training_data
cd ..

rm -rf out/comment_data
./scripts/comment_data.sh
cd out
tar cvzf $DATE-comment_data.tgz comment_data
cd ..

rm -rf out/tactic_benchmark
./scripts/tactic_benchmark.sh --aesop
