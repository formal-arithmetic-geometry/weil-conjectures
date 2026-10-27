## Worker report

The module Sheaf.AlgebraicGeometry.IndependentTorusCharacterValues states
AlgebraicGeometry.exists_torus_point_of_independent_characters, with its entire
proof postponed by sorry. There are no new definitions or dependency modules,
and no statement correction or disputed statement.

Hypothesis and conclusion correspondence:

- The algebraically closed field F is `(F : Type u) [Field F] [IsAlgClosed F]`.
  No characteristic hypothesis is imposed.
- The affine F-group scheme is `(T : Grp (Over (Spec (.of F))))
  [IsAffine T.X.left]`. The bundled `Grp` supplies exactly the group-object law,
  and `Over` supplies the base morphism.
- The nonnegative rank and number of characters are `(r m : ℕ)`.
  `hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r)` says that T is
  isomorphic AS A GROUP SCHEME to the recorded r-fold product of G_m.
  The existing node def-sfb-tori-multiplicative-type is added to stmt_deps
  to cite this already-landed definition, rather than defining another product.
- The characters are `χ : Fin m → (T ⟶ Grp.mk
  (StandardGroupSchemes.multiplicative F))`. Morphisms in Grp are precisely
  group-scheme homomorphisms; no additional pointwise-only assumption substitutes
  for that condition.
- Integer independence is `hind : ∀ n : Fin m → ℤ,
  (List.ofFn (fun i : Fin m ↦ (χ i).hom.hom ^ n i)).prod = 1 →
  ∀ i, n i = 0`. This is the identity of scheme morphisms, not just equality
  on F-points. The Hom group has pointwise multiplication and integer powers;
  `1` is the constant identity morphism. `List.ofFn` enumerates every Fin m
  index exactly once in order. An ordered product expresses the displayed
  product without requiring an unexported IsCommMonObj instance for G_m.
  The target G_m is commutative mathematically, so this has exactly the stated
  meaning. The underlying morphism functor is faithful, so forgetting the
  bundled homomorphism proof in this equality loses no information.
- The prescribed tuple is `(c : Fin m → Fˣ)`, including every nonzero scalar.
- The witness `t : Over.mk (𝟙 (Spec (.of F))) ⟶ T.X` is exactly an F-point of T.
- For every `i : Fin m`, `(t ≫ (χ i).hom.hom).left = Spec.map
  (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id F) (c i)))`
  says that chi_i(t) is the F-point of the actual recorded G_m whose Laurent
  coordinate is c_i. `eval₂` fixes the coefficients in F and sends t to c_i
  and t^(-1) to its inverse; this uses the unit itself, with no arbitrary map
  or unspecified identification. Both sides are scheme morphisms Spec F -> G_m;
  equality here is equivalent to equality as F-points.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs, extending CommRing and
  DivisionRing, with no restriction on the characteristic.
- def-weil-algebraic-closure: the relevant component is `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic, whose defining field says every polynomial
  splits; `IsAlgClosed.exists_root` gives the equivalent nonconstant-root condition.
  This is available through the algebraic-closure import of ToriMultiplicativeType.
  The theorem requires an algebraically closed F, not a chosen algebraic closure.
- def-sc-group-scheme: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`,
  `CategoryTheory.IsMonHom` and `CategoryTheory.Hom.group`, in
  Mathlib.CategoryTheory.Monoidal.Grp and .Cartesian.Grp, as documented by
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. `Grp` morphisms wrap
  `Mon.Hom`, enforcing the group homomorphism condition.
- def-sc-gm-ga: `StandardGroupSchemes.multiplicative` and `multiplicativeGroup`,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes; the former is `affine F
  (LaurentPolynomial F)`, the latter is the actual Laurent Hopf group structure.
  The affine and map constructions and their signatures/docstrings were read.
- def-sfb-tori-multiplicative-type: `MultiplicativeType.splitTorus`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType, recursively the tensor unit
  in rank zero and G_m tensor the rank-n product in rank n+1. Its tensors
  are cartesian products of group objects over Spec F.
- Proof dependency lem-sfb-pid-submodule-smith-bases:
  `Submodule.exists_smith_normal_form_of_le`, Mathlib.LinearAlgebra.FreeModule.PID,
  is imported privately. Its signature gives n <= o, bases of O and N and
  `(bN i : M) = a i • bO (Fin.castLE hno i)`, without assuming equal ranks.
- Proof dependency lem-sfb-split-torus-hom-matrices currently has no Lean record;
  no module import is available for that proof-only node. It is named in the
  proof docstring and does not supply data needed to type this statement.

Edge cases checked before writing:

- m = 0: List.ofFn is empty, its product is 1, independence and the conclusion's
  indexed equalities are vacuous; the identity F-point provides the witness.
- r = 0: splitTorus is the trivial group, every character is trivial, so the
  independence hypothesis forces m = 0. No positive-rank hypothesis is added.
- Positive characteristic dividing an exponent: surjectivity still holds by
  existence of polynomial roots, without assuming separability or distinct roots.
- A nonprimitive independent character, such as x -> x^p in characteristic p,
  is allowed; independence is not replaced by a direct-summand hypothesis.
- A trivial character with m > 0 violates hind (take exponent 1 at that index),
  as required. No independence condition is imposed on the prescribed c_i.
- The universe u is explicit and unrestricted; F and all schemes use the standard
  same-universe scheme convention. `autoImplicit false` is set explicitly.

Searches for an existing statement and definitions:

- msearch.py leanfinder: "Independent characters of a split algebraic torus over
  an algebraically closed field attain arbitrary nonzero values" returned eight
  results (CharacterModule separation, MulChar separation, Ax-Grothendieck,
  UnitAddTorus Fourier separation, Hilbert90, number-field embeddings and normal
  bases). None states this theorem on algebraic group schemes.
- msearch.py loogle: "GrpObj, IsMonHom, torus" returned zero hits and unknown
  identifier GrpObj. The actual GrpObj and IsMonHom sources were inspected directly.
- msearch.py grep: "torus|Torus|independent.*character|character.*independent"
  in AlgebraicGeometry returned zero hits.
- msearch.py leansearch: "Independent characters of a split algebraic torus attain
  all tuples of units over an algebraically closed field" returned eight results
  about MulChar, number-field units, roots of unity and analytic tori, no match.
- rg over lean/WeilConjectures for torus/Torus and character-independence patterns
  found no algebraic-torus statement; grep/rg for this blueprint id found no hit.
- rg over lean/Sheaf found the existing ToriMultiplicativeType.splitTorus and
  the existing multiplicative-character interfaces, which were read. No theorem
  prescribing values of independent torus characters was found.
- rg over Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json for
  independent_torus_character_values / independentTorusCharacterValues found
  no collision. Full declaration name
  AlgebraicGeometry.exists_torus_point_of_independent_characters is new.

Source checked directly with pdftotext on literature/milne-algebraic-groups_iAG2017.pdf:
Theorem 12.9 on printed pp.233--234 (PDF pp.245--246) identifies diagonalizable
morphisms with lattice maps; Proposition 23.7 on printed p.486 (PDF p.498)
chooses a torus point with the specified simple-root values. As the node says,
the independent-character generalization is the agent's lattice-extension
argument, not a literal quotation of Theorem 12.9. The theorem docstring carries
all five steps of that argument, including the Smith bases and negative exponents.

Validation: scompile.py compiled the sandbox probe and final module successfully
on the server with no errors or warnings (11.7s and 9.4s). The initial Finset.prod
form failed to synthesize CommMonoid; replacing only its product encoding by the
ordered list product repaired this without adding an assumption or declaration.

## Second reading by Q124

A final in-thread rereading matched the statement against the module and the node;
no independent reader or sub-agent was started, as instructed by the dispatcher.
Field, algebraic closedness, affineness, group-scheme splitting, arbitrary finite
character family, the full integer-relation test, arbitrary prescribed units,
and the F-point witness with every evaluation equality all match. In particular,
hT lives in Grp (not just schemes), hind is equality of morphisms (not just points),
and the conclusion's Laurent evaluation fixes F. Rank-zero and empty-family cases
are retained. No mismatch remains after the product encoding repair.
