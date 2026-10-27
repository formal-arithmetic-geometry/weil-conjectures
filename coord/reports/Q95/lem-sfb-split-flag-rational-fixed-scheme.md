## Worker report

The delivery states `AlgebraicGeometry.SplitFlag.split_flag_rational_fixed_scheme` in
`Sheaf.AlgebraicGeometry.GroupScheme.SplitFlagRationalFixedScheme`. Its only postponed proof
is the whole theorem, `by sorry`. The docstring carries all six proof steps and their DAG
references. Two definition modules supply missing interfaces with actual data and no sorry.
The original item's mathematical statement, proof and proof dependencies are unchanged.

Clause-by-clause correspondence:

- Arbitrary field F: `{F : Type u} [Field F]`; no algebraic-closedness, perfectness or
  characteristic assumption is present. H, T, B are `Grp (Over (Spec (.of F)))`, hence actual
  group schemes. Their operations and homomorphisms are Mathlib's group objects.
- Reductivity: `hH : ReductiveTorusCentralizer.IsReductive H`, the recorded smooth affine
  finite-type/geometrically connected/no geometric smooth connected normal unipotent
  subgroup predicate. It is used without substituting semisimplicity.
- T subset B subset H: `iT`, `iB`, `jB` and `hTB : jB ≫ iB = iT`. `hT` gives the closed
  maximal torus inclusion, `hTs` gives an actual finite-rank splitting. `hB : IsFieldBorel iB`
  supplies the closed smooth connected solvable maximal subgroup property. `hBs` uses the
  recorded `IsSplitSolvable`, including its finite smooth connected normal series and actual
  fppf Ga/Gm quotients. No rational-point version of solvability is substituted.
- Represented fppf quotient Q: `Q`, `π`, `hQ : IsCosetQuotient iB π`. This predicate is the
  actual sheafification universal property of the right-coset presheaf. Its coequalizer
  maps are projection and `(g,b) ↦ g iB(b)`. The unit equation pins the quotient map to π.
  Test schemes versus affine F-algebras give equivalent sheafifications: affine schemes
  form a basis and fppf coverings admit affine refinements. Between affines, locally finite
  presentation is finite presentation. Thus the topology is precisely the stipulated fppf
  algebra-covering topology, not a topology permitting arbitrary faithfully flat covers.
- Every L/F: the first conjunct quantifies over `[Field L] [Algebra F L]` and uses the
  recorded `MultiplicativeType.baseChange`. It asserts maximality, existence of a split
  torus isomorphism, the Borel predicate, and split solvability for the extended pair.
  All objects use one common ambient universe, as the recorded scalar-extension API does;
  the theorem is universe-polymorphic. No equality of distinct site universes is imposed.
- Scheme normalizer: existential `N`, `iN` with `IsClosedSubgroupScheme iN.hom.hom`, and
  its image on every commutative algebra is exactly `Normalizes iT g`. That condition is
  equality of conjugated torus images after *every* algebra homomorphism. The closed
  inclusion is monic, so this identifies the represented functor, not just its image on
  field-valued points. `j ≫ iN = iT` is the canonical inclusion T subset N.
- Weyl quotient: `W`, `p` and `SolvableGroupStructure.IsFppfQuotient j.hom.hom p` retain the
  actual quotient map, its flat-surjective-lfp property and its scheme-theoretic kernel T.
  This is the already recorded normal-group quotient definition, appropriate here because
  T is normal in N. It is not used for the nonnormal flag quotient H/B.
- Finite constant group scheme: `Finite (𝟙_ _ ⟶ W.X)` and
  `IsIso (Sigma.desc (fun w : 𝟙_ _ ⟶ W.X ↦ w))`. This is the canonical evaluation isomorphism
  from the finite coproduct of Spec F indexed by W(F). A group scheme with that underlying
  scheme is the constant group scheme on W(F), since each component of its product and
  inverse maps is determined by its rational point. This formulation fixes the labeling
  canonically instead of postulating an unrelated abstract finite Weyl group.
- Surjectivity N(L) → W(L) and bijectivity W(F) → W(L): the next universally quantified
  conjunction uses the base-changed group homomorphism p and `extendPoint`. The latter
  uses the canonical monoidal unit comparison for scheme pullback, so it is exactly the
  scalar-extension map, not an arbitrary bijection. In particular L = F gives representatives.
- Choose n_w: the remaining statement quantifies over *every* family n of F-rational
  N-points satisfying `n w ≫ p.hom.hom = w`. Such a family exists by the preceding
  surjectivity at F and ordinary choice. No multiplicative choice is demanded.
- Entire closed fixed subscheme: `RepresentsFixed iT π (Sigma.desc ...)` asserts a closed
  immersion of the coproduct of Spec F indexed by W(F), and, for every commutative
  F-algebra A, equivalence between universal fixation and unique factorization of the
  A-point through that very immersion. Its w-component is exactly `n w ≫ iN.hom.hom ≫ π`.
  `IsFixed` checks left multiplication on every local lift after every algebra extension;
  a quotient point need not itself lift. Local existence of lifts and the sheaf condition
  make this equivalent to the canonical quotient-action fixed condition: refine to lift,
  apply the condition there, and descend the equality. Nonreduced algebras are included.
- Same points after every L/F: the next `RepresentsFixed` uses the actual pullback of π,
  the recorded base-changed torus inclusion, and `Sigma.desc` of the scalar extensions
  of the *same* coset points. The domain is the coproduct of Spec L indexed by W(F).
  Thus it identifies all of `(Q_L)^(T_L)` as a reduced disjoint union, including nilpotent
  tests; it is not merely a bijection on L-rational points.
- H = T: `IsIso iT` expresses equality of subgroup schemes without insisting their
  presentations be literally equal. It implies `W ≅ Grp.trivial _`, `Q ≅ Spec F`, and that
  the canonical fixed-coset immersion is an isomorphism. Thus Q^T = Q = Spec F.

Recorded dependency declarations used:

- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`, `.IsMaximalTorus`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.baseChange`, `.splitTorus` (and `.IsTorus` inside
  the recorded maximal-torus predicate).
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `AlgebraicGeometry.SolvableGroupStructure.IsSolvable`, `.IsFppfQuotient`.
- `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`:
  `AlgebraicGeometry.IsSplitSolvable`, whose definition uses `SplitSolvableLength`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp`, `.GrpObj`, `.Hom.group`;
  `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`: `Algebra`.
  `StandardGroupSchemes.affine` and `.map` are reused for algebra-valued points.
- New supporting declarations: `AlgebraicGeometry.IsFieldBorel` and
  `AlgebraicGeometry.SplitFlag.IsCosetQuotient`, `.Normalizes`, `.IsFixed`,
  `.RepresentsFixed`, `.extendPoint`, in the two new modules listed below.

Already stated proof-dependency modules are imported privately:
`ReductiveTorusSelfCentralizer`, `SplitSolvableTorsorsAndVariety`,
`GroupScheme.ReductiveBorelPairStructure`, and `FpqcClosedImmersionDescent`.
The fpqc representable descent leaf is Mathlib's subcanonical fpqc topology in
`Mathlib.AlgebraicGeometry.Sites.Fpqc`, exposed by the interface module. The other proof
nodes currently have no recorded Lean declaration and therefore no module to import.

Edge cases checked by reading the predicates: rank-zero split torus and length-zero split
series use the recorded trivial groups; the case H = T is explicitly asserted; W(F) is
nonempty because W is a group scheme with identity; no nonempty-index assumption is added
to the coproduct construction. Empty test schemes/zero test algebra and nonreduced test
algebras are quantified over. No assumption says quotient points lift rationally: all lifts
in the fixed predicate are tested after arbitrary algebra extensions. All characteristics
and inseparable field extensions are allowed. No hypothesis becomes vacuous on those cases.

Searches: msearch.py leanfinder query "The torus fixed subscheme of a split flag variety is
the constant Weyl group scheme" returned only RootPairing Weyl group declarations; loogle
"IsBorelGroupScheme, normalizer, fixedPoints" returned no match; grep
"normalizer.*torus|torus.*normalizer|fixed.*flag|flag.*fixed" returned no match. LeanSearch
for the represented fppf quotient/normalizer/fixed functor returned abstract Sylow fixed
cosets, group normalizers, and invariant representations, not group-scheme functors.
Additional searches for each new notion, with exact returned output, are stored in its
`mathlib_searches`. Direct rg of WeilConjectures and Sheaf and grep of the DAG found only
an algebraically closed Borel definition, normal-group quotient predicates, and inline
quotient universal properties in existence theorems. No exact existing statement was found.
`blueprint_refs.py search 'split flag'` returned no blueprint nodes; searches by Borel and
normalizer do not provide the arbitrary-field/general quotient interfaces.

Source checked directly in the local Milne PDF, converted to text in the sandbox: Chapter
21 explicitly says the field is arbitrary; Proposition 21.1 states finite constancy and
rational representatives for every extension; the paragraph before 21.70 states that the
fixed scheme is finite constant. No statement correction or dispute is needed.

Validation: scompile.py compiled every delivered file separately, both as a sandbox file
and as its module, with no errors or warnings. No global build or direct Git command was run.

## New nodes

`def-sfb-field-borel-subgroup`: `Sheaf.AlgebraicGeometry.GroupScheme.FieldBorel` defines
`AlgebraicGeometry.IsFieldBorel`. Its only purpose is the arbitrary-field maximal smooth
connected solvable closed subgroup convention explicitly used by this item (Milne,
Definition 17.6 and Chapter 21, p.424). The existing `def-sfb-borel-subgroup-scheme` and
`IsBorelGroupScheme` require an algebraically closed field and use the other recorded
solvability interface, so importing them cannot type the present arbitrary-field statement.
This is a distinct general-field notion, with the same specialization, not a replacement
of the algebraically closed node. Searches are recorded verbatim in the new node.

`def-sfb-split-flag-functors`: `Sheaf.AlgebraicGeometry.GroupScheme.SplitFlagFunctors`
defines the nonnormal right-coset quotient universal property, universal normalization,
universal fixed points, closed representation of that functor, and the canonical scalar
extension of rational points. Sources: Milne, Definition 5.20, Proposition 21.1 and Section
21h; the fixed functor is also described in Section 7b. Existing normal quotient definitions
cannot describe H/B as B is usually nonnormal; existing abstract fixed-point constructions
and algebraically closed flag theorems do not supply these reusable scheme-theoretic
interfaces. The new predicates explicitly retain the existing group operations, fppf
site, scheme pullback and closed-immersion definition. No existence theorem or unknown
object is hidden in a definition. Searches are recorded verbatim in the new node.

## Second reading by Q95

A separate self-review pass reopened the item, both new definition-node statements and all
three modules. The dispatcher forbids starting other agents; this section records that
self-review, not an independent reader. The maintainer supplies the independent review.
The pass checked all clauses against the correspondence above, especially that the
normalizer is tested on algebra extensions, the quotient is fppf sheafification rather
than pointwise rational cosets, the finite-constant evaluation map is canonical, arbitrary
representatives give the specified closed immersion, and the L-version uses the same
points. It confirmed the source's arbitrary-field setting, preserved H = T and rank zero,
and checked all five interface declarations for real data. No mismatch was found.
