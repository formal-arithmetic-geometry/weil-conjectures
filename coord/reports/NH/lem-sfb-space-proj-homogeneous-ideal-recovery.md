## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProjHomogeneousIdealRecovery` states
`AlgebraicGeometry.AlgebraicSpace.space_proj_homogeneousIdeal_recovery`, with one
postponed proof and no definitions. The node is unchanged except for `lean`.
Read Stacks spaces-divisors.tex, lemma-closed-subscheme-proj, Tag 085L, including
its proof and reduction to divisors.tex Tag 0801. The node deliberately asks for
its existential consequence, not the stronger specification of the canonical
kernel in Stacks. The docstring follows all seven accepted DAG proof steps.

Hypotheses and conclusion, clause by clause:

- The base scheme is `{S : Scheme.{u}}`; the algebraic space is
  `{X : AlgebraicSpace S}`. The explicit universe `u` is exactly the existing
  scheme and algebraic-space convention: the small-etale category has objects
  in `u+1`, morphisms and section carriers in `u`. There is no imposed equality
  between independently variable site and coefficient universes.
- `A : SpaceProjInput X` contains `piece : ℕ → X.Modules`, the existing
  `EtaleGradedModuleAlgebra piece` (commutative, unital, O-linear homogeneous
  operations), and `quasiCoherent : ∀ n, (piece n).IsQuasicoherent`.
- `C : SpaceProjCoefficients S` and `R : SpaceProjSystem C` designate the
  normalized coefficient realization and Proj with all scheme tests from
  lem-sfb-space-relative-proj-scheme-tests. `Q : SpaceProjQuotientSystem C R`
  designates its canonical quotient maps. These are the existing coordinated
  realizations, not additional restrictions on S, X, A or Z: the dependency
  theorems assert their existence. The result holds for every such realization.
- `hqc` quantifies over every S-scheme `W : Over S` and morphism
  `g : schemeSpace W ⟶ X`. If `W.left` is affine, the scheme
  `(spaceProjScheme W (C.scheme A W g).affine).left` is compact. By the
  cartesian scheme-test comparison `R.realization A |>.cartesian`, this is
  exactly quasi-compactness of the source of the pullback of p over every
  affine scheme, as the node defines it. It assumes no compactness of X.
- `Z : AlgebraicSpace S` and `i : Z ⟶ (R.realization A).space` give the
  arbitrary closed subspace. `hi : IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom` says exactly that each
  scheme test is represented by a closed immersion. It includes the scheme
  structure, not just the underlying closed subset.
- The conclusion chooses a graded quasi-coherent quotient `B : SpaceProjInput X`
  and `φ : EtaleGradedModuleAlgebra.Hom A.algebra B.algebra`.
  `hφ : ∀ n, Epi (φ.degree n)` means surjectivity of the module sheaf in each
  degree, not pointwise surjectivity on all etale objects. In the abelian
  category of module sheaves an epimorphism is the cokernel of its kernel;
  hence this is exactly a presentation of B as A/I, with its quotient map.
  The Hom's multiplication and unit equations identify B's algebra operations
  with the quotient operations. This existential presentation avoids creating
  a duplicate quotient notion or choosing an arbitrary map on Proj.
- The homogeneous ideal is explicitly `I_n = kernel (φ.degree n)`, with
  inclusion `kernel.ι (φ.degree n)`. These are actual module subobjects; their
  inclusions are monic by the kernel construction. The first conjunct is
  `∀ n, (kernel (φ.degree n)).IsQuasicoherent`, exactly quasi-coherence of I_n.
  The total homogeneous ideal is the coproduct of these degree pieces, in the
  same sense as the existing graded-algebra convention. No claim that sections
  commute with infinite coproducts is used.
- The second conjunct quantifies over m, n, every etale chart V, an A_m section
  a, and an I_n section t. It requires an I_(m+n) section c whose image under
  its kernel inclusion is `A.algebra.mul m n V a (kernel.ι ... t)`.
  Thus it states explicitly `A_m I_n ⊆ I_(m+n)` as an inclusion of subsheaves,
  not merely a pointwise/radical ideal condition. Commutativity is in A's
  existing graded algebra structure. Degree zero is included.
- Finally `∃ e : (R.realization B).space ≅ Z,
  e.hom ≫ i = Q.map φ hφ` identifies the quotient Proj with Z as closed
  subspaces of the original P. `Q.map` is precisely the already normalized
  quotient-induced closed immersion; its specification fixes its scheme-test
  action. The equation retains both the ambient embedding and all nilpotents.
- There is no quasi-compactness or quasi-separatedness of X, finite presentation
  of i, finite generation or degree-one generation of A, or extra assumption
  on A_0, the characteristic, reducedness, nonemptiness or the base ring.

Dependency declarations used (their full signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `.IsRepresentableWith`, `.EtaleSite`, `.Modules` and their underlying site.
- `def-weil-size-convention` is a convention record, with no declaration.
- `Sheaf.TraceFormula.EtaleGradedModuleAlgebra`:
  `AlgebraicGeometry.AlgebraicSpace.EtaleGradedModuleAlgebra` and `.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh` and its underlying Mathlib
  `SheafOfModules.IsQuasicoherent` predicate (the class and local-presentation
  data in Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean were read).
- `Sheaf.AlgebraicGeometry.SpaceRelativeProjSchemeTests`:
  `SpaceProjInput`, `SpaceProjCoefficients`, `SpaceProjSystem`,
  `SpaceProjRealization`, `spaceProjScheme`, and
  `exists_space_relativeProj_scheme_tests`, all in namespace
  `AlgebraicGeometry.AlgebraicSpace`. Read the entire module, including its
  normalized section, pullback and scheme-test interfaces.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, used on scheme tests.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus`:
  `AlgebraicGeometry.AlgebraicSpace.quasiCoherent_affine_chart_calculus`;
  it imports the module-kernel calculus and supplies the quotient/kernel
  interpretation used here, with the existing commutative-algebra sheaves.
- `Sheaf.AlgebraicGeometry.SpaceRelativeProjQuotientClosedImmersion`:
  `SpaceProjQuotientSystem` and `space_relativeProj_quotient_closedImmersion`,
  whose `map`, `specification`, `unique` and `closedImmersion` fields give the
  exact canonical immersion, in namespace `AlgebraicGeometry.AlgebraicSpace`.

All already recorded proof-dependency modules are imported, including the
Mathlib match for Proj separatedness. Two proof-only dependencies have no Lean
record or mathlib_match yet (`lem-sfb-space-qcoh-kernels-colimits` and
`lem-sfb-space-relative-proj-graded-twists`); their future imports are omitted.
They are not needed to type this statement. No dependency repair is necessary.

Edge cases checked before writing:

- Empty X or empty scheme tests cause no choice of points or standard-open
  generators in the statement. The compactness condition allows empty schemes.
- Empty P and empty Z are allowed; no Nonempty condition occurs.
- For Z empty, use the zero quotient, so its kernel is all of A. No proper-ideal
  condition excludes this case. For Z=P the identity quotient has zero kernel;
  the proof's canonical kernel can alternatively contain irrelevant torsion.
- Arbitrary A_0 and A concentrated in degree zero (hence empty Proj) are allowed.
- Nonreduced closed subspaces are retained by an isomorphism commuting with
  closed immersions, never replaced by equality of topological supports.
- No finite set of homogeneous generators or bound on degrees is assumed.

Searches made with the prescribed msearch.py wrapper:

1. leanfinder: `Every closed subspace of quasi compact relative Proj is Proj of
   a quotient by a quasi coherent homogeneous ideal`. Eight hits, including
   Proj, its finite-type quasi-compactness/properness instances, and
   ProjectiveSpectrum.isClosed_iff_zeroLocus; none states recovery of arbitrary
   closed subspaces of space relative Proj.
2. loogle: `"Proj", "Ideal"`. Twelve hits, mainly ProjectiveSpectrum's
   vanishingIdeal and its zeroLocus properties, plus unrelated Lie ideals.
   Read vanishingIdeal's definition/docstring and isClosed_iff_zeroLocus in
   Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean: these describe
   underlying closed sets via radical ideals, and lose nonreduced structure.
3. grep: `([Hh]omogeneous.*[Ii]deal|[Pp]roj.*quotient)` in
   AlgebraicGeometry/ProjectiveSpectrum. Twenty-two hits, covering homogeneous
   prime ideals, localization and topological Proj constructions; no match.
4. rg in lean/WeilConjectures and lean/Sheaf for HomogeneousIdeal, GradedIdeal,
   homogeneous ideals, Proj quotients, recovery, and the intended declaration
   name; grep for the node id in lean/WeilConjectures. No exact declaration.
   Read `exists_projectiveClosedSubscheme_homogeneousIdeal` in
   Sheaf.AlgebraicGeometry.ProjectiveClosedSubschemeHomogeneousIdeal: it is
   specific to polynomial projective space over one ring and is not this
   relative arbitrary graded algebra/algebraic-space statement. The existing
   graded Hom and categorical kernel notions suffice; no new definition.

Validation: prescribed scompile.py compiled both sandbox and library module
successfully (4.1 s and 4.9 s). No errors or non-sorry warnings. Both automatic
implicit options are disabled and the declaration name has no existing match.

## Second reading by NH

A second pass reread the node, all nine statement-dependency records, the actual
module signatures, and the full delivered theorem. The dispatcher explicitly
prohibits starting other agents, so this is the same worker's second pass,
not a claimed independent review; the maintainer's independent delivery review
is still required.

The checked correspondence is: scheme S and space X binders; SpaceProjInput for
all degrees and quasi-coherence; normalized C/R for P and p; all affine scheme
tests in hqc; arbitrary space Z and representable closed immersion hi; degreewise
kernel subobjects for I; first conjunct for their quasi-coherence; second
conjunct for homogeneous product closure; epi homogeneous quotient φ for A/I;
canonical Q.map and the commuting isomorphism for equality as closed subspaces.
All clauses and edge cases listed above match. In particular the result does
not assert the stronger canonical-kernel formula that the node omitted, does
not substitute pointwise surjectivity for an epi of sheaves, and does not assume
quasi-compactness of the base. No statement correction, added definition or
unusable dependency was found.
