## Worker report

The module `Sheaf.Paper.EtaleLowerTruncationFlatModel` states
`AlgebraicGeometry.Scheme.etale_lower_truncation_flat_model`. Its one proof is
`sorry`; no construction is postponed and no definition is added. The item's
only changed field is `lean`. There are no new nodes, dependency modules, or
statement corrections. No repair note for this item was present.

Source read: `literature/stacks-project/sites-cohomology.tex`, the complete
proof of `lemma-bounded-below-tor-amplitude` (Tag 0F1M), especially the displayed
lower truncation, kernel, and flat-image sequence. The node is the elementary
truncation-and-kernel part of that proof, without the additional K-flatness
hypothesis on the original complex used later in the source.

Hypotheses and constructions, clause by clause:

- The scheme is `(T : Scheme.{u})`; the arbitrary commutative coefficient ring
  is `(Λ : Type (u + 1)) [CommRing Λ]`. Neither nontriviality nor any
  characteristic, finiteness, Noetherian, or separation restriction is imposed.
- The site is exactly `T.smallEtaleTopology`. Its object universe is `u + 1`
  and its morphism universe is `u`. It is small in universe `u + 1`; its
  equivalent small model implements the chosen-skeleton convention. The
  coefficient ring and module values are both in that universe. This is the
  same universe convention and module-sheaf encoding as `etale_kflat_criteria`.
- The constant commutative ring sheaf is
  `(constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
  (CommRingCat.of Λ)`. Its image by `sheafCompose` with the forgetful functor
  to `RingCat` is the argument of `SheafOfModules.{u + 1}`. These are actual
  Mathlib constructions, not an arbitrary ring sheaf or a chosen substitute.
- `K : CochainComplex (...) ℤ` supplies integer-indexed terms, differentials
  with square zero, and module-linear chain maps. `(a : ℤ)` is unrestricted.
- `hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite ... (K.X i)` is termwise
  tensor flatness in the recorded definition. Its explicit universe arguments
  are site objects, site morphisms, coefficients, and modules, respectively.
- `hvanish : ∀ i : ℤ, i < a → IsZero (K.homology i)` states precisely the
  vanishing below `a`; no vanishing at `a` is assumed.
- `hquotient` asserts flatness of `K.opcycles a`. This is the cokernel of
  `K.d (a - 1) a`, with its own canonical projection `K.pOpcycles a`:
  `HomologicalComplex.opcyclesIsCokernel` supplies its cokernel universal
  property. It is the node's `N`, not the cohomology object `H^a(K)`.
- The specified complex `P` is the existing `K.truncGE a` from
  `def-kun-truncations`. It has zero terms below `a`, the opcycles object at
  `a`, and retained terms above `a`, under the standard truncation
  isomorphisms `K.truncGEXIsoOpcycles a` and `K.truncGEXIso a i hi`.
  `HomologicalComplex.truncGE'_d_eq_fromOpcycles` gives the induced outgoing
  differential; the other retained differentials are unchanged.
- The specified `q` is `K.πTruncGE a`, not an existential or arbitrary map.
  The construction in `Embedding/TruncGE.lean` extends
  `restrictionToTruncGE'`: it is zero below the bound, the opcycles projection
  at the boundary, and the identity on retained terms under those same
  standard identifications. Thus these clauses are rendered by using the
  recorded canonical definition, without restating it.

Conclusion, in the order of the conjunctions:

1. `QuasiIso (K.πTruncGE a)` is the assertion that the specified quotient map
   induces isomorphisms on all cohomology sheaves.
2. `∀ i, IsFlatOnSite ((K.truncGE a).X i)` asserts flatness of every term of P.
3. `kernel (K.πTruncGE a)` is L, the kernel in the category of complexes.
   `HomologicalComplexLimits` computes these limits degreewise. For `i < a`,
   `IsIso ((kernel.ι (K.πTruncGE a)).f i)` identifies its term with `K.X i`
   through the actual inclusion. Under that identification the inclusion is
   the identity. The kernel inclusion is already a chain map, so earlier
   differentials are exactly the retained differentials of K.
4. The existential `e : L.X a ≅ image (K.d (a - 1) a)` identifies the boundary
   term with I. Its first equation identifies the kernel inclusion with the
   canonical image monomorphism. Its second equation explicitly says
   `L.d (a - 1) a ≫ e.hom = inclusion.f (a - 1) ≫ factorThruImage ...`:
   under the preceding retained-term identification this is exactly the
   node's image factorization of the incoming differential. The compatibility
   prevents an unrelated abstract isomorphism from replacing the inclusion.
5. `IsFlatOnSite (image (K.d (a - 1) a))` is I flat.
6. `∀ i, a < i → IsZero (L.X i)` asserts all remaining terms are zero and
   supplies the explicit upper bound a. In particular the outgoing
   differential from the boundary, and all later differentials, vanish.
7. `∀ i, IsFlatOnSite (L.X i)` states that L has flat terms.
8. `CochainComplex.IsKFlatIndependentCoefficients L` is exactly the recorded
   ringed-site K-flat predicate: for every acyclic F, the direct-sum total
   tensor F tensor L is acyclic. No boundedness restriction is placed on F.
9. `∀ i, ((ShortComplex.kernelSequence q).map (HomologicalComplex.eval ... i)).ShortExact`
   is the degreewise sequence with arrows `inclusion.f i` and `q.f i`,
   including its monomorphism, exactness, and epimorphism assertions. It is
   the sequence L to K to P, not a separate sequence with unrelated objects.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology`; its underlying
  `Scheme.Etale` is defined in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-size-convention` is recorded as a metatheoretic convention with
  no declaration; the explicit universes above render it.
- `Mathlib.Algebra.Homology.Additive`:
  `CategoryTheory.Functor.mapHomologicalComplex`, recorded for the composite
  `def-kun-constant-sheaf`; the actual constant ring used here is its
  underlying `CategoryTheory.constantSheaf` from
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`, as specified by that record.
  No constant complex is needed in this item.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex` and its
  morphisms, as recorded by `def-pc-cochain-complex-modules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, using `CategoryTheory.exactFunctor` of
  the canonical `SheafOfModules.siteSheafTensorRight`.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.homology` and `HomologicalComplex.Acyclic`, the
  definition and characterization recorded by `def-pc-acyclic-complex-modules`.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` publicly exposes
  `CochainComplex.truncGE` and `CochainComplex.πTruncGE`, together with the
  standard term identifications from
  `Mathlib.Algebra.Homology.Embedding.CochainComplex`.
- `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- Proof-only imports are the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatQuotientTensorSES`
  (`SheafOfModules.flat_quotient_tensor_shortExact`),
  `Sheaf.Paper.EtaleKFlatCriteria`
  (`AlgebraicGeometry.Scheme.etale_kflat_criteria`), and
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
  (`AlgebraicGeometry.Etale.derivedTensor`). Their stated roles are respectively
  flatness of I, bounded-above K-flatness, and the signed tensor convention.
  They are imported without `public`; no derived tensor object appears in
  the signature and no comparison between the module-sheaf encodings is assumed.

The module docstring and theorem docstring explain all five steps of the DAG
proof, naming their dependency nodes. The only new declaration is the theorem;
all canonical maps and objects use existing definitions.

Edge cases checked mathematically:

- The zero complex, the zero coefficient ring, and an empty scheme are allowed.
  Nothing assumes a nonzero image or nonzero cokernel.
- A flat sheaf in degree a has q an isomorphism and zero kernel. A flat sheaf
  in degree a+1 is likewise retained. A nonzero sheaf only in degree a-1
  fails precisely `hvanish`, so the theorem does not mistakenly assert q is
  a quasi-isomorphism there.
- The contractible two-term complex F --id--> F in degrees a-1,a has N=0,
  P=0 and L=K with I=F, consistent with every clause.
- Multiplication by 2 on the constant integers in degrees a-1,a has flat
  terms and vanishing homology below a, but nonflat cokernel, and is excluded
  by `hquotient`. Thus this flatness assumption has real mathematical content.
- For positive, zero, and negative a, the incoming differential is always
  `K.d (a - 1) a`. No natural-degree or bounded-below restriction was introduced.
- The hypothesis imposes no upper bound on K; only its kernel is bounded
  above. No K-flatness of K or P has been added to the hypotheses or conclusion.

Searches made on 2026-10-21, using the prescribed msearch.py wrapper:

- LeanFinder, query “Good lower truncation of a flat sheaf complex with flat
  cokernel has bounded above flat K-flat kernel”: 8 results about cohomological
  bounds and truncations, including `DerivedCategory.isGE_Q_obj_iff` and
  `HomologicalComplex.instIsStrictlySupportedTruncGE_1`; no complete match.
- Loogle, query `CochainComplex.truncGE, "quasiIso"`: 5 results, including
  `CochainComplex.quasiIso_πTruncGE_iff`; these give the quasi-isomorphism part,
  without the flat-image and K-flat kernel clauses.
- Grep of Mathlib, query `truncGE.*[Ff]lat|[Ff]lat.*truncGE|KFlat|kFlat`:
  no hits. The truncation definitions and homology declarations were then
  inspected directly at the paths above.
- LeanSearch, query “A good lower truncation of a complex of flat module
  sheaves with flat cokernel has bounded above flat K-flat kernel”: 8 results,
  including `CochainComplex.quasiIso_ιTruncLE_iff` and
  `HomologicalComplex.shortComplexTruncLE_shortExact`; no complete match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, query
  `lower.truncation.flat|truncGE.*[Ff]lat|[Ff]lat.*truncGE|lem-kun-lower-truncation-flat-model`:
  found `affine_flat_connective_truncation` on quasi-coherent finite-presentation
  O_S-modules with universal pullback hypotheses, and the private
  `truncGE_flat` in `IntegralCanonicalTruncations` on flat homology of derived
  pro-etale objects. Their full signatures were read; neither says this
  etale constant-ring, complex-kernel statement.
- `grep -rn` of the item id in `lean/WeilConjectures`: no hit. `rg` of the new
  theorem name in both source trees and `dag/lean_names_upstream.json`: no hit.

No statement dispute or source error was found. Validation uses scompile.py for
this individual module and deliver2.py for the server preflight and final compile.

## Second reading by Q14

Author's self-check, with the DAG node, Stacks source and final Lean signature
open; the independent review is left to the maintainer as the dispatcher brief
requires. The three mathematical assumptions are termwise flatness, homology
vanishing strictly below a, and flatness of the boundary cokernel. Their Lean
binders above match them individually. I checked each of the nine conclusion
clauses against the node, including the actual kernel inclusion and its
boundary differential, rather than only an abstract existence of a complex.
The kernelSequence evaluated in degree i has exactly the required terms and
maps. The standard truncation and quotient definitions supply the described
P and q without an extra choice or universal property hypothesis.

The initial compile exposed an inference failure for flatness of the kernel
terms; explicit universe levels fix it without imposing universe equalities.
The reading also made the image-factorization equation explicit beside the
boundary isomorphism. No node statement changed, no conclusion was dropped,
and no hypothesis that K itself is K-flat was inserted.
