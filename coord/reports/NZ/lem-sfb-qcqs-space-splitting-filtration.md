## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQcqsSplittingFiltration` states
`AlgebraicGeometry.AlgebraicSpace.exists_qcqs_splitting_filtration`, with its proof
postponed by `sorry`. No new definition, helper theorem, dependency module or
statement correction is needed. The mathematical statement is unchanged.

Source read: `literature/stacks-project/decent-spaces.tex`,
`lemma-filter-quasi-compact-quasi-separated` (Tag 07ST), and
`literature/stacks-project/spaces-limits.tex`, `proposition-approximate` (Tag 07SU),
first proof paragraph. The former supplies the finite filtration and splitting;
the latter explicitly supplies the final chart isomorphism. The declaration's
docstring gives all six steps of the node's natural-language proof and names its
supporting DAG lemmas.

Clause-by-clause correspondence:

- The base is exactly Spec Z: `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`.
  `ULift` places the integers in the arbitrary scheme universe `u`; it does not
  restrict the base or the size of the spaces. The metatheoretic size convention
  is implemented by the explicitly bound universe `u` and the existing big-site
  algebraic-space category. No size equality or smallness assumption is added.
- X is quasi-compact: `hqc : CompactSpace (Point X.obj.obj)`, with the existing
  final atlas topology. CompactSpace means finite-subcover compactness and
  imposes no Hausdorff assumption. X is quasi-separated:
  `hqs : IsAbsolutelyQuasiSeparated X`. This existing affine-pair test is
  equivalent to quasi-compactness of the absolute diagonal over Spec Z, as its
  definition node and Stacks 0AHR specify. It is not relative quasi-separatedness
  over a possibly non-quasi-separated arbitrary base.
- There is an integer n >= 1: `∃ m : ℕ`, with source index n = m+1. Every positive
  integer occurs and length zero is impossible. The source's p in 1,...,n is
  represented by the Lean index p-1 in `Fin (m+1)`.
- The quasi-compact open subspaces are `U : Fin (m+2) → OpenSubspace X` and
  `∀ p, CompactSpace (Point (U p).val.toFunctor)`. Their source endpoints are
  `(U 0).val = ⊤` and `(U (Fin.last (m+1))).val = ⊥`. Their inclusions are
  `∀ p : Fin (m+1), U p.succ ≤ U p.castSucc`. The order is precisely the recorded
  inclusion order of open subfunctors. Inclusions need not be strict.
- The schemes are `V : Fin (m+1) → Over (Spec (.of (ULift.{u} ℤ)))`.
  Each underlying scheme satisfies `CompactSpace (V p).left` and
  `(V p).left.IsSeparated`, Mathlib's absolute closed-diagonal separatedness.
- The displayed f_p has its actual source and target:
  `f p : yoneda.obj (V p) ⟶ (U p.castSucc).val.toFunctor`.
  `IsEtale (f p)` is the recorded *representable* etale scheme-test predicate,
  and `IsSurjective (f p)` is the recorded surjectivity predicate on all scheme
  tests. Thus representability is included, not silently omitted.
- The reduced closed stratum T_p is an algebraic space `T p` with map
  `t p : (T p).obj.obj ⟶ (U p.castSucc).val.toFunctor`.
  `IsRepresentableWith (fun _ _ q ↦ IsClosedImmersion q.left) (t p)` gives its
  closed-subspace structure, `IsReduced (T p)` its reduced structure, and
  `pointImage (t p) = mapPoint (U p.castSucc).val.ι ⁻¹'
    (pointImage (U p.succ).val.ι)ᶜ` gives exactly U_p minus U_{p+1}, in the point
  space of U_p. A reduced closed immersion with this support is the unique
  reduced induced structure: on etale affine charts its defining ideal is
  radical. This uses the existing reducedness definition, not a new reduced
  complement or an arbitrary closed structure. The support equivalence is the
  one supplied by `exists_unique_reduced_closed_subspace` (Tag 03IQ).
- The map V_p ×_{U_p} T_p → T_p is literally
  `Limits.pullback.snd (f p) (t p)` in the presheaf category. Its `IsIso` clause
  specifies the canonical projection, not an arbitrary isomorphism of objects.
  Sheaf fibre products and algebraic-space fibre products agree by the recorded
  dependency. Using underlying presheaves does not change this property.
- The final map is `IsIso (f (Fin.last m))`. Together with compactness and
  absolute separatedness of its scheme source this says precisely that U_n is
  a quasi-compact separated scheme. No reducedness of U_n or V_n is asserted.
- All relative quasi-compactness, relative quasi-separatedness, affine-morphism,
  local finite type and finite presentation descriptions in the introductory
  convention paragraph determine terminology. The theorem quantifies over no
  additional morphisms with those properties, so they create no extra premise
  or conclusion. Scheme-test closed immersions and representable etaleness
  are used exactly as specified, with no chart-only weakening of etaleness.

Dependency declarations used (source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec` and `Spec.map` (the latter is the recorded spectrum functor interface).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace` and its
  inherited inclusion order.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`
  and `pointImage`, on `Point` from `AlgebraicSpacePointClasses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsLocallyOfFinitePresentation`, `MapIsSeparated` and the other recorded
  property definitions supply the introductory conventions and are imported.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli` (publicly imported by the preceding
  property module): `mapPoint` is the canonical induced point map;
  `MapIsQuasiCompact` supplies the affine-test convention.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` gives the agreement of sheaf fibre products
  with the algebraic-space category; the statement uses `Limits.pullback`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, used by `IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`, the existing landed definition node
  `def-sfb-space-absolute-quasi-separated`, added to stmt_deps.
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace`: `IsReduced`, the existing
  landed definition node `def-sfb-reduced-algebraic-space`, added to stmt_deps.
  These additions cite existing notions; no node other than the item is edited.

All currently recorded project proof-dependency modules are plainly imported:
AlgebraicSpaceEtaleOpenImage, AlgebraicSpacePointOpenCalculus,
SpaceSeparatedLqfPermanence, AdmissibleFreeFiniteQuotient,
ReducedClosedSubspaceSupport, SpaceSeparatedEtaleDiagonalComplement,
SpaceEtaleSourceAtlasDetection, AlgebraicSpaceRepresentableEtaleSchemeTests,
and upstream EtaleFibreDiscreteSeparablePoints. The Mathlib proof inputs are
available through the public dependencies. The four proof-only nodes
`lem-sfb-etale-atlas-distinct-tuple-geometry`,
`lem-sfb-qc-space-affine-etale-atlas`,
`lem-sfb-separated-lqf-affine-finite-set`, and
`lem-sfb-space-qc-etale-fibre-bound` currently have no recorded module, so no
module import can be given for them. They are named in the proof docstring;
they are not needed to elaborate the statement and are not replaced here.

Edge cases checked before writing and again on reading the Lean:

- X empty: m=0, both opens empty, V_0 the empty scheme, T_0 empty and both
  projection and final map isomorphisms; no nonemptiness binder forbids this.
- Length one: m=0 gives exactly two endpoint opens and one chart; U_n=X and the
  final chart is an isomorphism, as required for that length.
- Empty intermediate strata, repeated opens and empty scheme charts remain
  allowed. Surjectivity forces an empty chart's target empty, as it should.
- Nonreduced X and opens are allowed: only T_p is required to be reduced.
  In particular the final chart is an isomorphism over U_n itself, not just its
  reduction. No finiteness, Noetherianity, characteristic or reducedness
  assumption has been added.
- The arbitrary universe u covers all scheme sizes in the chosen big site;
  there is no independent test-scheme universe that could make tests vacuous.

Searches (actual wrapper logs are in searches.jsonl):

- LeanFinder via msearch.py: "Quasi compact quasi separated algebraic spaces
  admit a finite splitting filtration of quasi compact open subspaces with
  separated etale scheme neighborhoods". Eight scheme-cover/affine-limit hits,
  including QuasiCompactCover and Scheme.exists_isOpenCover_and_isAffine;
  none states this algebraic-space splitting filtration.
- Loogle via msearch.py: `"AlgebraicSpace", "filtration"`. Zero hits.
- Mathlib grep via msearch.py: `splitting.*filtration|AlgebraicSpace|filter.*[Ee]tale`
  under AlgebraicGeometry. One unrelated EtalePoint cofilteredness instance.
- LeanSearch via msearch.py: "A quasi compact quasi separated algebraic space
  has a finite splitting filtration by open subspaces with separated etale
  scheme charts". Eight scheme quasi-separatedness hits, including
  quasiSeparatedSpace_iff_quasiCompact_prod_lift; none is the statement.
- rg in both lean/WeilConjectures and lean/Sheaf for the item id,
  `splitting[Ff]iltration|splitting_filtration`: only two proof-docstring
  references to this missing statement (AlgebraicSpaceConstructibleAffineEtaleTest
  and SpaceQcqsDistinguishedSquareInduction), no declaration.
- rg across AlgebraicSpace*.lean, Space*.lean and *Reduced*.lean for reduced
  closed support, quasi-compactness, quasi-separatedness and OpenSubspace located
  the existing interfaces listed above. They are reused rather than duplicated.

Validation: scompile.py compiled the sandbox module and its library-named form
cleanly on the server (2.1 s and 2.0 s); no errors or non-sorry warnings.
All binders are explicit, with `set_option autoImplicit false`. No diagnostic
commands remain. No STATEMENT-DISPUTED issue or source/node fault was found.

## Second reading by NZ

I performed a separate second pass with the original node JSON and final Lean
signature open. No other agent was started, following the dispatcher's explicit
instruction; the maintainer's independent review remains separate from this pass.

The base and qcqs hypotheses match exactly. I checked the index translation
source p = Lean p.val+1: `castSucc` is U_p, `succ` is U_{p+1}, and `Fin.last m`
is the final chart f_n. Top and bottom apply to the underlying subfunctors,
so they really are X and the empty subspace; the order is non-strict inclusion.
The compactness quantifier covers all n+1 opens, and the scheme-condition and
etale/surjectivity quantifier covers exactly the n charts. The stratum's support
is a subset of the U_p point space, obtained by inverse image along its inclusion
into X; it is not an accidentally ambient complement in X. Reducedness plus the
closed immersion fixes the reduced closed structure and keeps nilpotents out of
T_p while allowing them in U_p. The pullback projection is the map to T_p,
and the last isomorphism is f_n itself. This recheck found no mismatch and made
no signature changes. The two added stmt_deps are existing landed definitions
for precisely the absolute quasi-separatedness and reducedness already present
in the natural-language statement; no extra hypothesis was introduced.
