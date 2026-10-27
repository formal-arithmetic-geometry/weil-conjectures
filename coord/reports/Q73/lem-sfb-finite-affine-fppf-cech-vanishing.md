## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteAffineFppfCechVanishing` states
`AlgebraicGeometry.Scheme.finite_affine_fppf_cech_vanishing`, with `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.
The source read is `literature/stacks-project/descent.tex`,
`lemma-standard-covering-Cech` (03FI) and
`lemma-standard-covering-Cech-quasi-coherent` (03FJ), including the displayed
Amitsur comparison and its faithfully flat exactness argument. The node requests
its fppf vanishing consequence; its six-step proof is included in the docstring.

Hypothesis and clause correspondence:

- Size convention: explicit universes `u w`, `Scheme.{u}`, its category `Over S`
  with object universe `u+1` and morphism universe `u`, module sections in `u`,
  and finite indexing type `I : Type w`. The cochain/cohomology category is
  `AddCommGrpCat.{max u w}`. No equality of object and morphism universes is imposed.
- Scheme S: `(S : Scheme.{u})`.
- Arbitrary quasi-coherent Zariski module F: `(F : SfbZariskiQCoh S)`.
  This full subcategory is defined using `SheafOfModules.isQuasicoherent`, not
  `IsQuasiCoherentFiniteType`; no finite type, coherence, or flatness is required.
- Associated module sheaf F^a: `(sfbAssociated S
  ((Classical.choose scheme_big_fppf_quasicoherent_equivalence) S)).obj F`.
  This chooses the equivalence from the existing theorem together with its
  section-normalized characterization; it is not a new arbitrary equivalence.
  The theorem supplies additive section equivalences to
  `Γ((Modules.tensorPullback U.hom).obj F.obj, ⊤)`, scalar compatibility,
  and exactly the restriction formula using `sfbSectionPullback`,
  `Modules.tensorPullbackSectionComp`, and the equality of composite structure
  maps in `Over S`. These determine the associated module sheaf up to the
  canonical module-sheaf isomorphism. In particular the choice retains its
  canonical restriction maps, not just abstract degreewise section groups.
  The existing consumer `AffineSchemeFppfQCohAcyclic` uses this identical witness.
- Affine object u:V→S: `(V : Over S) [IsAffine V.left]`; its structure map is
  `V.hom`. No affineness of S is assumed.
- Finite family of affine objects and arrows over V: `{I : Type w} [Finite I]`,
  `(Vᵢ : I → Over S) [∀ i : I, IsAffine (Vᵢ i).left]`,
  `(g : ∀ i : I, Vᵢ i ⟶ V)`. The `Over` morphisms include compatibility with S.
- The fppf covering hypothesis is `hcover`: membership of the presieve of
  `(g i).left` in `fppfPrecoverage V.left`. That precoverage is the jointly
  surjective precoverage of flat locally finitely presented arrows, exactly
  the three covering conditions, without requiring each arrow surjective.
- The chosen tuple fibre products are `(D : SiteCechComplex Vᵢ g)` in `Over S`.
  Its universal properties give products over the object V, whose underlying
  schemes are the fibre products over V.left in the statement. The choice is
  unrestricted subject to those universal properties and the degree-zero
  identity normalization. This is the interface explicitly required by the
  existing dependency record, not a new geometric assumption.
- Underlying abelian sheaf: `.val.presheaf` of the associated module sheaf,
  i.e. the underlying additive presheaf of its presheaf of modules; the module
  object already carries the fppf sheaf condition. This is definitionally the
  presheaf of `SheafOfModules.toSheaf`.
- Displayed degree-p product and alternating omitted-factor differential:
  `D.cohomologyFunctor p` uses `D.complexFunctor`; `D.cochains` is the product
  over `Fin (p+1) → I`, and `D.differentialValue` is the signed restriction
  sum using `D.indexMap t j.succAbove`. Applying the associated-sheaf section
  comparison identifies every factor with the stated pulled-back sections.
  The common structure map is projection to the first member followed by its
  map to V and V.hom, as required.
- Every positive p: `(p : ℕ) (hp : 0 < p)`.
- Zero Cech cohomology: `IsZero ((D.cohomologyFunctor p).obj ...)`, the zero
  object predicate on the actual abelian cohomology group, kernel modulo image.
- No Noetherian, separatedness, finite generation, or flatness hypotheses on
  S or F occur anywhere in the signature.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes Mathlib's
  `SheafOfModules.IsQuasicoherent`; its finite-type conjunction is not used.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over` supplies the slice.
- `Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence`:
  `SfbZariskiQCoh`, `sfbAssociated`, `scheme_big_fppf_quasicoherent_equivalence`,
  and the section and normalized restriction characterization in its full signature.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Modules.tensorPullback`, `tensorPullbackSectionAdjunction`,
  `tensorPullbackSection`, `tensorPullbackSectionComp`, `tensorPullbackSectionId`.
- `WeilConjectures.CategoryTheory.SiteCechComplex`: `SiteCechComplex`,
  `SiteCechComplex.cochains`, `differentialValue`, `complexFunctor`,
  `cohomologyFunctor`. The convention node has no separate definiendum.

Proof-dependency imports also include the recorded upstream quasi-coherent
pullback theorem; `AlgebraicGeometry.flat_iff`; finite-product flatness via
`Module.Flat.directSum`, `Module.Flat.of_linearEquiv`,
`DirectSum.linearEquivFunOnFintype`; `sigmaSpec` and `ι_sigmaSpec`;
`Module.FaithfullyFlat.of_comap_surjective`; `pullbackSpecIso` and its projection
formulas; `Modules.exists_tensorPullback_affine_sections`; `TensorProduct.piLeft`;
`Modules.nonempty_tensorPullbackId` and `nonempty_tensorPullbackComp`; and
`Module.FaithfullyFlat.exact_amitsurComplex`. Their signatures/docstrings were
read in the recorded modules. These are plain imports; statement dependencies
are public imports. The explicit tensor pullback's quasi-coherence follows by
comparison with the upstream left adjoint, as also supplied in the big-fppf
equivalence's base-restriction clause.

Edge cases checked before writing: I may be empty, with no `Nonempty` or
positive-cardinality hypothesis. Then the cover forces V empty, and there are
no tuples `Fin (p+1) → I`, so every cochain group is the zero empty product.
An empty individual member has zero coordinate ring and zero section module;
the affine tensor and finite-product comparisons remain valid. Empty S and the
zero module are allowed. A singleton cover gives the usual Amitsur complex,
including identity covers. Nonflat modules and infinitely generated modules
remain in `SfbZariskiQCoh`. Degree zero is deliberately not claimed to vanish:
an identity cover of a nonzero module has its sections as H^0. The fibre
products use the affine target V, so nonseparated S causes no issue. The finite
index may live in any universe w; finite products introduce only `max u w` in
abelian groups, without restricting the geometrical site or coefficients.

Searches run:

- `msearch.py leanfinder`, query `The Cech cohomology of a quasi coherent module
  vanishes for finite affine fppf covers`: 8 hits, including
  `SheafOfModules.QuasicoherentData.coversTop`, local presentation declarations,
  and affine-limit section lemmas. None states the vanishing theorem.
- `msearch.py loogle`, query `"Cech", "exact"`: 0 hits.
- `msearch.py grep`, query `fppf.*[Cc]ech|[Cc]ech.*fppf|[Aa]mitsur`: 0 Mathlib hits.
- `rg -n 'fppf.*[Cc]ech|[Cc]ech.*fppf|finite_affine_fppf|finiteAffineFppf'`
  in `lean/WeilConjectures` and `lean/Sheaf`: only the affine refinement theorem
  and a proof-docstring reference in the affine acyclicity consumer. Neither
  states finite-affine-cover Cech vanishing.
- `grep -rn 'lem-sfb-finite-affine-fppf-cech-vanishing' lean/WeilConjectures`:
  no hit. The existing general Cech definition and Amitsur exactness theorem
  are used, rather than restated.

Validation: the initial scompile.py run elaborated the module in sandbox and
library contexts; it reported only a 101-character line. That line was split
before the final compile and delivery preflight. The only postponed proof in
this module is the assigned theorem. No statement dispute or node fault found.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
