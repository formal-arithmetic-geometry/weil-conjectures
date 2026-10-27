## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FieldParabolicQuotientRationalLift`
states `AlgebraicGeometry.field_parabolic_quotient_rational_lift`, with one theorem
and its stage-2 `sorry`. There are no new definitions, auxiliary postponed lemmas,
new nodes, dependency repairs, or statement corrections. The item JSON changes
only `lean`. Every variable and universe is explicit, with `autoImplicit false`.

Source read: Milne, Algebraic Groups (2017), Theorem 25.9 and its proof, printed
p.546, including its reference to the open opposite cell (13.33), rational density
(17.93), and Lang's theorem (17.98). Theorem 25.9(b) explicitly covers both finite
and infinite fields. The module docstring carries all seven DAG proof steps,
including the quotient identification, kernel formula and descent of the cell open.

Hypotheses, individually:

- Any field k: `{k : Type u} [Field k]`. There is no `Infinite`, `Perfect`,
  `IsAlgClosed`, characteristic, or splitness assumption.
- G and P are k-group schemes: `G P : Grp (Over (Spec (.of k)))`. Their internal
  group structures provide multiplication, inverse, identity and natural group
  structures on every test-scheme Hom set.
- G is reductive: `hG : ReductiveTorusCentralizer.IsReductive G`, using the exact
  dependency declaration. Its definition includes affine finite type, smoothness,
  connectedness after algebraic closure and triviality of smooth connected normal
  unipotent closed subgroups there. Its unipotence is the faithful matrix predicate
  from `SolvableGroupStructure.IsUnipotent`, not a pointwise or reduced substitute.
- The closed subgroup inclusion is `i : P ⟶ G` with
  `[IsClosedSubgroupScheme i.hom.hom]`. A morphism of bundled group schemes
  preserves the group operations; this class includes the underlying closed
  immersion, hence identifies P with its image on all test schemes.
- P is smooth: `[Smooth P.X.hom]`.
- P is geometrically connected: `hP` is `ConnectedSpace` on the underlying scheme
  of `(MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj P`. This is the
  same scalar-extension convention as the recorded reductivity definition.
- The proper finite-type representative is `Q : Over (Spec (.of k))` with
  `[IsProper Q.hom]`. The exact dependency's Mathlib convention is used: proper
  is separated, universally closed and locally finite type; universal closedness
  supplies quasi-compactness, hence finite type. No finiteness clause is omitted.
- The canonical quotient arrow is `q : G.X ⟶ Q`. Its specified natural map `ηq`
  starts at the coequalizer of `yoneda.map (fst G.X P.X)` and the right
  multiplication map `yoneda.map (fst G.X P.X * (snd G.X P.X ≫ i.hom.hom))`.
  Colimits of Type-valued presheaves are pointwise, so this is the presheaf of
  right cosets G(T)/P(T), without assuming P normal.
- The equation `hηq : coequalizer.π _ _ ≫ ηq = yoneda.map q` identifies q with
  the canonical coset projection, rather than an arbitrary arrow into Q.
- `hquot` asserts that precomposition with `ηq` is bijective for maps into every
  fppf sheaf Z. This is exactly the sheafification universal property. The target
  `yoneda.obj Q` is an fppf sheaf by Mathlib's subcanonical fppf topology and its
  over-site; therefore this does not omit the target sheaf condition. On affine
  tests this is the stated sheaf of commutative k-algebras for faithfully flat
  finitely presented covers. The big fppf site has the same affine restrictions:
  affine covers refine any scheme cover, and over affine sources and targets
  locally finite presentation is finite presentation. This is the same
  coequalizer/universal-property encoding used in the already landed modules
  `HomogeneousOrbitQuotientGeometry` and `StandardParabolicLeviCharts`, without
  adding a duplicate quotient definition or a torsor assumption.

Conclusions, individually:

- The left action exists as `∃ a : ModObj G.X Q, ...`. `ModObj` includes unit and
  associativity and is a morphism of schemes, so naturality is built in. Its
  normalization `μ[G.X] ≫ q = (𝟙 G.X ⊗ₘ q) ≫ a.smul` is precisely
  q(ag)=a·q(g) on every test scheme. This normalization identifies it with left
  multiplication on cosets.
- Faithful flatness is `Flat q.left ∧ Surjective q.left`.
- Finite presentation is `LocallyOfFinitePresentation q.left ∧ QuasiCompact
  q.left ∧ QuasiSeparated q.left`, retaining the global finiteness conditions.
- The right P-torsor isomorphism is `∃ e : G.X ⊗ P.X ≅ pullback q q` with
  `e.hom ≫ pullback.fst q q = fst G.X P.X` and second projection equal to
  `fst G.X P.X * (snd G.X P.X ≫ i.hom.hom)`. These specify the actual map
  (g,p)↦(g,gp), not merely an unspecified isomorphism of the two objects.
- For every commutative k-algebra A, including nonreduced and zero algebras,
  `g ≫ q = (1 : StandardGroupSchemes.affine k A ⟶ G.X) ≫ q ↔
  g ∈ Set.range (fun p ↦ p ≫ i.hom.hom)` is the asserted fibre P(A) over q(1).
  `StandardGroupSchemes.affine k A` is the existing actual Spec(A) over k.
- Rational surjectivity is `Function.Surjective (fun g : 𝟙_ (Over
  (Spec (.of k))) ⟶ G.X ↦ g ≫ q)`. The terminal k-scheme is Spec k, so its Hom
  sets are exactly G(k) and Q(k). This is not surjectivity onto abstract cosets.

Dependency declarations read and used:

- `Field`: Mathlib.Algebra.Field.Defs, class extending CommRing and DivisionRing.
- `CategoryTheory.Grp`, `CategoryTheory.GrpObj`:
  Mathlib.CategoryTheory.Monoidal.Grp. The group-scheme interpretation and
  `IsClosedSubgroupScheme` are in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`:
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology. Its full
  definition and its SolvableGroupStructure/MultiplicativeType dependencies were
  read. The same existing scalar extension is used for hP.
- `AlgebraicGeometry.IsClosedImmersion`:
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion, used through the subgroup
  class (closed embedding and surjectivity on stalks).
- `AlgebraicGeometry.IsProper`:
  Mathlib.AlgebraicGeometry.Morphisms.Proper, including its documented finite-type
  convention.
- `AlgebraicGeometry.LocallyOfFiniteType`, `QuasiCompact`:
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact, used through
  properness and through the reductive affine-algebraic-group predicate.

All recorded proof-dependency modules available on the read base are imported
privately: HomogeneousQuotient (the full `exists_homogeneousQuotient` statement
was read), EnlargedEtaleRingedSite, AlgebraicSpaceFpqcSheaf,
AffineGroupDualNumberCalculus, Smooth, FppfLocalOpenSubfunctorDescent. The Mathlib
proof leaves fppf cover base change and fppf-to-fpqc comparison come from Fpqc.
The four proof dependencies split-torus-hom-matrices,
parabolic-prescribed-split-cocharacter, relative-dynamic-subgroups, and
infinite-field-reductive-rational-density, and the finite-field-connected-group-
torsor-point node have no Lean module on the read base; no import is invented.
Their mathematical use remains in the full theorem proof docstring.

Edge cases checked before writing: P=G (quotient Spec k, torsor identity formula
still correct); trivial G=P; anisotropic reductive groups (no proper parabolic
required); finite fields (Lang case); imperfect infinite fields (density uses
reductivity, no perfectness); nonnormal P (Q is not a group object); nonreduced
algebras (Hom sets retain nilpotents); zero algebra (the empty affine scheme has
one point in each functor of points); arbitrary characteristic and rank zero.
All test rings use the existing common universe u, as do the recorded scheme and
scalar-extension constructions; no independent smaller test universe is introduced.

Searches actually run:

- msearch leanfinder: `Parabolic quotient of a reductive group over any field is
  a torsor and all rational cosets lift`. Eight hits: modular cusp maps,
  `OnePoint.exists_mem_SL2`, `MulAction.isPretransitive_quotient`, etc.; none is
  the scheme-theoretic result over any field.
- msearch loogle: `"parabolic", "surjective"`. Zero hits.
- msearch grep: `[Pp]arabolic|[Cc]oset[Ss]heaf` in AlgebraicGeometry. Zero hits.
- msearch leansearch: `Parabolic subgroup reductive algebraic group rational
  quotient map surjective over any field`. Eight hits: abstract group quotient
  surjectivity, modular forms, rational maps; none is the present theorem.
- rg in project Sheaf and upstream WeilConjectures for parabolic/Parabolic,
  cosetSheaf/CosetSheaf, and parabolic quotient/lift/surject patterns; found the
  two existing algebraically closed/split-root-data statements described above,
  which do not cover any field and hence cannot replace the item. Exact item-ID
  search in WeilConjectures and upstream-name index returned no declaration.
- DAG definition search for right-coset and fppf quotient terminology found the
  existing solvable-group structure definition, which only covers normal group
  quotients. No new definition was needed: the present statement uses the
  general Mathlib presheaf coequalizer and sheafification universal property
  directly, in the same format as the landed homogeneous-quotient statements.

No statement fault or disputed assertion was found. Initial server compile was
clean. The node's Lean signature is copied verbatim from the final module.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
