## Worker report

The module `Sheaf.Paper.ExternalEvaluationTransposeNatural` states
`AlgebraicGeometry.Etale.ExternalRHom.external_evaluation_transpose_natural` with `sorry`.
No definition, dependency record, natural-language statement, or DAG edge is changed.
No new node is needed. I read the entire item, its nine proof steps, all ten statement
dependencies and their recorded interfaces, and Stacks `sites-cohomology.tex`,
`lemma-internal-hom` (08J9) and `lemma-restriction-RHom-to-U` (08JB), including their proofs.
No repair note exists for this item.

### Hypotheses and clauses

* The commutative ring is `(A : Type (u + 1)) [CommRing A]`. Every scheme is
  `Scheme.{u}`. This is the recorded ordinary constant-coefficient presentation on
  essentially small small-etale sites, with modules and site objects in the common
  universe `u + 1`; derived categories live in `u + 2`. No independent smaller test
  universe or coefficient restriction is introduced.
* `DerivedCategoryModule A T` is exactly
  `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  All `G,M,E,K,H,L` and primed objects are arbitrary objects of this unbounded category.
  There are no boundedness, flatness, finite-type, properness, or torsion hypotheses.
* The existing `ExternalRHom.globalHom A T` is the internal-Hom bifunctor followed by
  `rightDerivedGlobalSections (ModuleCat A) T`: its value is precisely the stated
  object H_T(G,M) in D(A). `constant A T` is the existing left-derived constant-sheaf
  functor; exactness identifies it with termwise constants. `pull A a` is the
  existing derived scheme inverse image, exact on ordinary module sheaves.
* The first conjunct is bijectivity of the explicit untranspose
  `f ↦ ((constant A T).map f ▷ G) ≫ evaluation A G M` for every T,G,M,Q.
  Its inverse is the existing `transpose`. Naturality of this bijection is already
  part of the actual `globalAdjunction` used to define `transpose`, composed from
  the recorded constant/sections and closed tensor/Hom adjunctions, with the
  canonical braiding moving the constant factor to the left. No arbitrary Hom
  equivalence or evaluation is assumed. The second conjunct explicitly says that
  transposing `evaluation A G M` gives the identity of H_T(G,M); consequently the
  bijection sends that identity to evaluation as required.
* `pairing A a b E K H L` is already defined on precisely C tensor D, with target
  H_P(a^*E tensor b^*H, a^*K tensor b^*L). It is `pairingOf`, hence `transpose` of
  `externalEvaluationOf` applied to the two `pulledEvaluation` maps. In the latter,
  `derivedConstantPullbackIso` identifies constants, `pullTensorIso` supplies the
  inverse-image tensor constraint, and `leftDerivedTensorComparison` supplies the
  constant tensor comparison. `tensorμ` interchanges the middle D and a^*E factors
  using the existing derived Koszul braiding. Thus its cochain interchange is
  exactly (-1)^(degree(z)*degree(e)). These are existing real definitions;
  construction and well-definedness are not replaced by an existence assertion.
* The third conjunct quantifies over all E,E',K,K',H,H',L,L' and all
  `f : E' ⟶ E`, `g : H' ⟶ H`, `s : K ⟶ K'`, `t : L ⟶ L'`. Its equation tensors
  `homMap A f s` and `homMap A g t` before the new pairing, or applies the old
  pairing before `homMap` of the pulled-back tensor maps. This gives exactly both
  contravariances and both covariances, simultaneously, with no hypotheses on the
  objects. The existing `IsNatural` predicate could not be used: it adds bounded-flat
  and bounded-below assumptions absent from this node.
* The fourth conjunct quantifies over an open `j : X' ⟶ X` and a pullback square
  `sq : IsPullback p a' a j`. A chosen representative of the pullback is equivalent
  to P'=P times_X X'; no preferred choice is required. `p` is k in the node and
  `p ≫ b` is b'. `RestrictionSquare ... j (𝟙 Y) ...` is the exact restriction
  equation, with `restriction` on global Hom, `pairing` on both sides, and
  `homMap` of the inverse source / forward target `restrictionTensorIso` components.
  The latter are built from `squarePullIso` and the pullback tensor isomorphism,
  so they give exactly k^*G and k^*F identifications in the question. The Y factor
  is transported along the canonical identity pullback; this expresses the
  unchanged factor in the common square interface.
* The fifth conjunct states the analogous Y square, now with
  `sq : IsPullback p b' b j`, first restriction `𝟙 X`, and first projection `p ≫ a`.
  There are again no boundedness or flatness assumptions. The existing
  `CommutesWithOpenRestriction` predicate is deliberately not used because it
  imposes such assumptions.
* `restriction A j E K` is not an arbitrary map: it is the transpose of
  `pulledEvaluation A j E K`, i.e. restriction of constant-source derived morphisms.
  For opens the slice comparison and sections counit calculation in proof steps
  5--6 identify it with the usual global derived-Hom restriction map.

### Dependency declarations and reuse

The following recorded declarations were read in their defining modules, with full
signatures and docstrings, and their modules are public imports (also transitively
available from the existing construction module).

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
* `def-weil-size-convention`: the record is a metatheoretic convention; explicit
  `u`, scheme universe u, and module universe u+1 implement it, not a Lean object.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`, with the actual definition
  in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar` and `Etale.upperStarLowerStarAdjunction`.
* `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `Etale.derivedTensor`, the
  canonical curried tensor of the existing K-flat-derived monoidal structure.
* `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the generic
  `derivedInternalHomOfUniverses` and its public ordinary-etale interface from
  `WeilConjectures.SixFunctors.Etale.Derived.Hom` (`derivedHom`,
  `derivedTensorHomAdjunction`). The latter are the closed internal Hom used by
  the existing `ExternalRHom.internalHom`.
* `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`:
  `derivedConstantGlobalSectionsAdjunction`, normalized constant monoidal
  instances and `etaleConstantSheaf_preservesFlat`.
* `Mathlib.Algebra.Homology.Additive`: `Functor.mapHomologicalComplex`, specialized
  to `constantSheaf` and `.up ℤ` for the exact termwise constant complex.
* `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
* `Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing`: the recorded public interface
  for `Etale.derivedConstantPullbackIso`, whose actual definition is in its public
  import `Sheaf.AlgebraicGeometry.OrdinaryKunnethMap`. Read that definition: derive
  the inverse ordinary constant comparison and compose with the exact-functor
  derived-composition iso. No finite-coefficient theorem is used.

Additional existing definitions, not a second construction: the public
`ExternalRHom` helpers in `Sheaf.Paper.ExternalRHomConePairing`, specifically
`globalAdjunction`, `transpose`, `evaluation`, `pullTensorIso`, `pulledEvaluation`,
`pairing`, `restriction`, `homMap`, `squarePullIso`, `restrictionTensorIso`, and
`RestrictionSquare`. Their bodies and docstrings were read. The existing parent
THEOREM is not used: its bounded-flat/bounded-below conclusion does not state this
unrestricted node. The new theorem has only `sorry` as its proof.

Import-cycle exception (stages/2-statements.md §3.7): this file imports the parent's
already existing definitions. Do not add the reverse proof-plan import from
`ExternalRHomConePairing` to this module, because that would close an import cycle.
The DAG is unchanged and no proof use of the parent theorem is made here. To use this
new theorem inside the parent's source during stage 3, the shared existing helpers
will need to be factored into a lower module by the maintainer; this delivery does
not copy, rename, or silently change those definitions.

All already stated proof-dependency modules are explicitly imported: the closed
ringed-site monoidal theorem, exact inverse image, ringed-slice evaluation theorem,
constant composition coherence, derived pullback composition monoidality, cochain
pullback tensor coherence, and etale inverse-image localization. The open-base-change
leaf comes from the imported Mathlib OpenImmersion module. The signed exact-pullback
comparison node has no Lean record yet, so there is no module to import for it; it is
not used as unintroduced data in the signature.

### Edge cases and searches

Checked before writing: empty schemes and empty opens are permitted; identity opens
are permitted; all four inputs may be zero; the coefficient ring may be the zero ring;
complexes may be unbounded in either direction and have no flat representative chosen
as data. Nothing excludes any of these cases. Naturality allows identity and zero
maps in all four variables. The naturality and restriction equations have the right
source/target variances, especially the inverse source comparison in `homMap`.

Searches made:

* `msearch.py ... leanfinder "The transpose of external pulled back derived Hom
  evaluations is natural and commutes with open restriction"`: eight hits, all
  scheme structure-sheaf restriction naturality, no match.
* `msearch.py ... loogle "AlgebraicGeometry.Etale.derivedHom"`: zero hits; Loogle
  does not know that project identifier. Its actual source was read locally.
* `msearch.py ... grep "external.*[Ee]val|external.*[Tt]ranspose"`: zero Mathlib hits.
* `rg` for `external.*evaluation`, `external.*transpose`, `globalDerivedHom` in
  both `lean/WeilConjectures` and `lean/Sheaf`: the scheme O_X-global-Hom family
  is a different coefficient notion. The exact external constructions are already
  in `Sheaf/Paper/ExternalRHomConePairing.lean` and were reused as above.
* `rg` for the item id in `lean/WeilConjectures`: no match. `rg` for the existing
  construction and item in DAG nodes found the parent and chain-model consumer.
  No declaration has the new unrestricted statement. In particular the parent
  theorem's hypotheses on `IsNatural` and `CommutesWithOpenRestriction` prevent
  an `existing: true` binding to it.

No STATEMENT-DISPUTED issue and no source correction. The first server compile of
this delivered theorem passed in sandbox and library modes (6.2s and 8.8s) without
warnings. The final file is checked again by the prescribed delivery dry run.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
