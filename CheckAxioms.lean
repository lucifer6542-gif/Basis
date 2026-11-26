import SquareBasis

/-! Prints the main statements and the axioms their proofs depend on.
Expected for every line: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). -/

-- Theorem 1.1
#check @SquareBasis.square_basis_theorem_paper
#print axioms SquareBasis.square_basis_theorem_paper
#print axioms SquareBasis.thm11

-- Figure 1
#print axioms SquareBasis.figure1

-- Section 2
#print axioms SquareBasis.lemma22
#print axioms SquareBasis.prop23a
#print axioms SquareBasis.prop23b
#print axioms SquareBasis.prop23b_full
#print axioms SquareBasis.prop23c
#print axioms SquareBasis.hasSquareBasis_dual_iff

-- Section 3
#print axioms SquareBasis.prop31
#print axioms SquareBasis.mem_ker_iff_split
#print axioms SquareBasis.step3
#print axioms SquareBasis.tensor_basis
#print axioms SquareBasis.forest_basis
#print axioms SquareBasis.sq1
#print axioms SquareBasis.sq2
#print axioms SquareBasis.sq3

-- Section 4
#print axioms SquareBasis.lemma41
#print axioms SquareBasis.lemma41_full
#print axioms SquareBasis.thm42
#print axioms SquareBasis.thm43
#print axioms SquareBasis.prop44_iff
#print axioms SquareBasis.thm45
#print axioms SquareBasis.thm46

-- Section 5
#print axioms SquareBasis.lemma51
#print axioms SquareBasis.lemma52
#print axioms SquareBasis.prop53

-- Section 6
#print axioms SquareBasis.lemma61
#print axioms SquareBasis.prop62
#print axioms SquareBasis.example63
#print axioms SquareBasis.example63_z

-- Section 7
#print axioms SquareBasis.cor71
#print axioms SquareBasis.cor71_height
#print axioms SquareBasis.codim_eq
#print axioms SquareBasis.cor71_exists
#print axioms SquareBasis.cor71_minimal
#print axioms SquareBasis.binom_square
#print axioms SquareBasis.thm74a
#print axioms SquareBasis.thm74b
#print axioms SquareBasis.thm74b_of_span
#print axioms SquareBasis.thm74_unique
#print axioms SquareBasis.thm74b_unique
#print axioms SquareBasis.remark75

-- Section 8
#print axioms SquareBasis.prop82

-- Tutte's theorem
#print axioms SquareBasis.tutte_minor
