## Worker report

Item: `lem-sfb-isogeny-torus-conjugacy` (NP, stage 2).
The new module `Sheaf.AlgebraicGeometry.GroupScheme.IsogenyTorusConjugacy`
states `AlgebraicGeometry.isogeny_torus_conjugacy`, with proof `sorry`.
It introduces no definition or auxiliary theorem. Only the item's `lean` record changes.

Source read: the local `literature/milne-algebraic-groups_iAG2017.pdf`,
Proposition 23.7, printed p.486 (including its displayed conjugation calculation),
and Theorem 23.25, printed pp.492--493; also the immediately preceding discussion
of root powers in 23.5. The node already uses the correct composition order:
`Int(t) ∘ a`. The last line of the proof of 23.7 reverses this order, whereas its
statement and display have the order used here. This is already noted by the
stage-1 review; no node correction is needed.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
  The universe `u` is declared, and `autoImplicit` is false.
- G₁ and G₀ are bundled group objects in `Over (Spec (.of F))`.
  `hG₁` and `hG₀` use `ReductiveTorusCentralizer.IsReductive`, exactly the
  predicate used by the recorded Borel-pair dependency. Its `IsAlgebraic`
  component means affine and finite type; it also asserts smoothness, geometric
  connectedness, and the absence of a nontrivial smooth connected normal
  unipotent subgroup after algebraic closure. Over algebraically closed F this
  is the node's reductivity. The nested `IsUnipotent` uses a faithful closed
  matrix representation and unipotence at geometric points.
- T₁ and T₀ are group schemes, with inclusions `i₁ : T₁ ⟶ G₁` and
  `i₀ : T₀ ⟶ G₀`. `hT₁` and `hT₀` use `IsMaximalTorus`, including the
  closed-subgroup, torus, and maximal-under-inclusion conditions.
- Splitting is `hsplit₁` and `hsplit₀`: existence of a natural rank and a
  group-scheme isomorphism to the dependency's `MultiplicativeType.splitTorus`.
  This is a property rather than an extra chosen splitting, and includes rank zero.
- `a b : G₁ ⟶ G₀` are group-scheme homomorphisms, by the bundled category.
  `ha` and `hb` are `Surjective` on their underlying scheme maps, not merely
  surjectivity on rational points and not a flatness hypothesis.
- `haker` and `hbker` are `IsFinite (GrpObj.ker ...).hom`. The recorded kernel
  is the fibre product with the identity section, so this retains the full
  scheme-theoretic kernel, including nilpotents. Finiteness of a scheme over F
  is equivalent to having a finite-dimensional coordinate algebra.
- Mapping the source torus into the target torus is expressed by actual
  restrictions `aT bT : T₁ ⟶ T₀` and the commuting equalities
  `i₁ ≫ a = aT ≫ i₀`, `i₁ ≫ b = bT ≫ i₀`. Since `i₀` is a closed inclusion,
  these restrictions are unique; supplying them is exactly the stipulated
  factorization as scheme morphisms, not an additional assumption.
- The characters are all bundled group-scheme maps
  `χ : T₀ ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)`.
  `hchars` says `aT ≫ χ = bT ≫ χ` for every such χ. This is precisely equality
  of character pullbacks as morphisms, not only of their values at F-points.
- The conclusion supplies `t : 𝟙_ (Over (Spec (.of F))) ⟶ T₀.X`, namely an
  F-rational point of the target torus. The unit object is Spec F over itself.
- Put informally `c = toUnit G₁.X ≫ t ≫ i₀.hom.hom`. The conclusion is
  `b.hom.hom = c * a.hom.hom * c⁻¹`, with c written out in the actual signature.
  The multiplication and inverse are the group structure on morphisms into G₀.
  Precomposing by any point x over any test algebra gives
  `b(x) = t_A * a(x) * t_A⁻¹`. Thus this is exactly `b = Int(t) ∘ a` as scheme
  morphisms. The faithful forgetful functor from group objects makes this also
  equality of group-scheme homomorphisms. No arbitrary conjugation map is used.
- There is no kernel smoothness, reducedness, separability, centrality, or
  characteristic restriction, and no nonempty-root hypothesis.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (the field Mathlib match).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the recorded algebraic
  closure module `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` is imported.
  `AlgebraicClosure` and its definition were also read; no replacement is defined.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, and
  bundled group homomorphisms. This is the group-scheme dependency's attachment.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` and
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`:
  `CategoryTheory.GrpObj.ker`, `AlgebraicGeometry.IsFinite`, and the group-scheme
  conventions. The kernel is the pullback of the homomorphism and the unit.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`:
  `AlgebraicGeometry.reductive_borel_pair_structure`. Its full signature and
  proof docstring were read. The statement uses its exact terminology, namely
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`,
  `MultiplicativeType.splitTorus`, and `StandardGroupSchemes.multiplicative`.
  Their defining modules `ReductiveTorusCentralizerTerminology`,
  `SolvableGroupStructure`, `ToriMultiplicativeType`, and `StandardGroupSchemes`
  were opened and their definitions read; no stronger root datum or Borel is
  introduced as a hypothesis here.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `GrpObj.Hom.group`, whose
  inverse is postcomposition with the group object's inverse morphism.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`, whose
  field is surjectivity of the underlying continuous map.

Plain proof imports are the recorded modules for
`lem-sfb-affine-homomorphism-flat-image`,
`sbc-lem-smooth-geometrically-reduced`, and
`lem-sfb-reductive-root-subgroup-parametrizations`; their declarations/docstrings
were read. The Borel-pair proof dependency is already a public import.
`lem-sfb-isogeny-root-power-laws`,
`lem-sfb-independent-torus-character-values`, and
`lem-sfb-isogeny-simple-root-rigidity` still have no Lean records in the read
repository, so no module is available to import for those proof-only inputs.
The docstring records every step and every one of those node ids for stage 3.
These are not prerequisites to typing this statement.

Edge cases checked before writing:

- Pure tori, including the trivial group and rank-zero tori: no root data are
  required as input. Equality of characters forces equality of torus maps;
  the identity torus point conjugates one to the other.
- Positive characteristic and Frobenius isogenies: a nonreduced finite kernel
  is permitted by `GrpObj.ker` and `IsFinite`; no differential, reduced kernel,
  or separability premise has replaced the scheme morphism hypothesis.
- Nonreduced test algebras: the conclusion is equality of morphisms, which
  pulls back to every test point, rather than equality only on closed points.
- Central torus factors are allowed: no root-spanning assumption is made.
  The conjugator is existential, without incorrectly asserting uniqueness in T₀.
- The restrictions and character comparisons are scheme-theoretic; no equality
  on points over an undersized auxiliary universe is used. All groups have the
  same scheme universe as F and no independent test universe can make a
  hypothesis vacuous.

Searches actually run with the prescribed msearch.py wrapper:

- LeanFinder: `Two isogenies of reductive algebraic groups agreeing on torus
  characters differ by conjugation by a point of the target torus`.
  Eight hits, including Galois-category automorphism uniqueness and abstract
  root-pairing equivalences; none compares group-scheme isogenies.
- Loogle: `"isogeny"`. Zero hits.
- Mathlib grep: `isogen|[Rr]eductive|torus.*conjug|conjug.*torus`, subdirectory
  `AlgebraicGeometry`. Zero hits.
- LeanSearch: `Two isogenies of reductive algebraic groups agreeing on a split
  maximal torus are conjugate by a torus element`. Eight hits, including
  `GroupExtension.IsConj` and Iwasawa-structure identities. Read
  `GroupExtension.IsConj`: it concerns splittings of abstract group extensions,
  not scheme isogenies. Read `RootPairing.Hom` in Mathlib as well; it is an
  abstract root-pairing structure, not this uniqueness result.
- Local rg across `lean/WeilConjectures` and `lean/Sheaf` for
  `isogeny.*torus|isogeny.*conjug|torus.*conjug|isogeny_torus|isogen.*unique`:
  found existing maximal-torus and cocharacter conjugacy modules, but no
  isogeny uniqueness theorem. Read the comparable conjugation formula in
  `CompleteDVRTorusCocharacterConjugacy` to check the morphism-group encoding.
- `grep -rn 'lem-sfb-isogeny-torus-conjugacy' lean/WeilConjectures`: no hits.
  `rg` of the chosen declaration name in upstream names, Mathlib and both
  project source roots: no collision.

Validation: scompile.py NP lem-sfb-isogeny-torus-conjugacy compiled this module
on the server successfully, including its live imports, with no errors or
warnings. Every delivered line is at most 100 characters. There is one named
postponed theorem and no new data definition. No statement dispute or node fault.

## Second reading by NP

Author's separate second pass, not an independent-agent review: the dispatcher
forbids starting other agents and assigns independent review to the maintainer.
Reopened the node and complete module and checked all binders against the
clauses above. In particular, both reductive hypotheses and both split maximal
tori are present; neither of the two surjectivity or finite-kernel hypotheses is
lost; `aT` and `bT` have the correct domain and codomain and the commuting squares
have the right composition order; characters are those of T₀, pulled back to T₁;
and the conjugator is a point of T₀, not G₁ or a quotient torus. Multiplication
is performed in `G₁.X ⟶ G₀.X`, so the conclusion is a morphism equality in the
correct category. The conclusion has b on the left and `Int(t) ∘ a` on the right.
No mismatch was found and no source statement change was made. The one sorry
has the entire five-step DAG proof in its docstring.
