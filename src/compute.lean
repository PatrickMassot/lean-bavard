import tactic.ring tactic.abel


namespace tactic.interactive
setup_tactic_parser

meta def compute_at_hyp' (h : name) : tactic unit :=
let lo := loc.ns [h] in
do { ring none tactic.ring.normalize_mode.horner lo <|>
norm_num [] lo <|>
abel tactic.abel.normalize_mode.term lo } ; try (`[dsimp only])

meta def compute_at_goal' : tactic unit :=
do focus (tactic.iterate_at_most 3 `[refl <|> ring <|> abel <|> norm_num] >>= list.mmap' (λ _, skip))

end tactic.interactive
