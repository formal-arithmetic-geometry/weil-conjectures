## Worker report

Record existing upstream `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso`
in `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`.
No module, new notion, dependency repair, or statement correction is required.
Read the declaration's full signature, its comparison construction, and their docstrings.

Hypotheses and clauses:
- Any scheme morphism u:U→V is `{Z Y : Scheme.{u}} (g : Z ⟶ Y)` with Z=U, Y=V.
  Neither etaleness of g nor any finiteness assumption is required.
- Any commutative ring Λ is `Λ : Type (u + 1)` with `[CommRing Λ]`, and the coefficient
  category is `ModuleCat.{u + 1} Λ`. This is the existing project size convention, not
  a ring restriction; universe cumulativity includes small rings, and universes can
  be enlarged to accommodate any coefficient ring and scheme.
- K,L in the unbounded D(V_et,Λ) are arbitrary objects of
  `DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  There is no boundedness, constructibility, or finite Tor hypothesis.
- The tensor is `Etale.derivedTensor`, recorded by def-kun-derived-tensor in
  `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, whose implementation is the
  K-flat derived tensor `curriedTensor` on the derived category.
- The inverse image on sheaves is the dependency's `Etale.upperStar`, in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. Its exact derived functor
  is `D(upperStar A g)`. The existing natural identification
  `Etale.leftDerivedUpperStarIsoMapDerivedCategory A g` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` identifies it with
  `L(upperStar A g)`, used by the tensor comparison.
- The recorded natural isomorphism runs from u⁻¹(K⊗ᴸL) to u⁻¹K⊗ᴸu⁻¹L.
  Its `.symm`, and at objects `leftDerivedUpperStarTensorIso A g K L |>.symm`,
  has exactly the direction displayed in the node.
- This is the canonical comparison, not merely existence of some isomorphism.
  `leftDerivedUpperStarTensorComparison` is the derived natural transformation of
  the ordinary oplax comparison δ, characterized by its square with the derived
  counits on homotopy-category representatives. The lemma
  `leftDerivedUpperStarTensorNatIso_hom` identifies it with the hom of this iso.
  The inverse ordinary comparison μ gives the node's canonical direction. On flat
  K-flat models this is the degreewise pullback tensor comparison totalized, as
  in Stacks 07A4, including the differential signs and direct sums.
- Being an iso in `D(V_et,Λ) ⥤ D(V_et,Λ) ⥤ D(U_et,Λ)` supplies simultaneous
  bifunctoriality in K and L; the inverse iso is likewise natural in both variables.

All auxiliary typeclasses on the general upstream declaration specialize without
extra hypotheses. In particular `upperStarPreservesFlat_moduleCat` in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat` supplies preservation
of flat sheaves for every commutative ring and arbitrary scheme morphism. Import
this module when specializing the recorded comparison to modules. This is a genuine
instance, proved by stalks, not an added assumption about u or Λ.

Source checked: local `literature/stacks-project/sites-cohomology.tex`,
label `lemma-pullback-tensor-product` (Tag 07A4), including the last total-complex
comparison in its proof. Also read both recorded statement dependency declarations.
The node proof specializes the ringed-topos comparison to constant coefficient
rings, uses exactness to identify derived pullback with inverse image, applies
07A4, and identifies the inverse comparison on K-flat flat-term models. These
are exactly the identifications encoded by the existing declarations above.

Edge cases checked: identity and arbitrary non-etale morphisms, empty schemes,
zero ring, zero complexes, and unbounded complexes. None is excluded by the
signature or module-ring instances. No flatness of Λ over another ring is assumed.

Searches made with msearch.py:
- leanfinder: `inverse image of etale sheaves commutes with derived tensor product`:
  eight unrelated hits (Kaehler differentials and underived sheaf pullback).
- loogle: `Functor.Monoidal, DerivedCategory.tensor`: zero hits, unknown identifier
  `Functor.Monoidal` reported by the service.
- grep Mathlib CategoryTheory: `upperStar.*[Tt]ensor|[Tt]ensor.*upperStar|derived.*[Mm]onoidal`:
  zero hits.
- leansearch: `inverse image commutes with derived tensor product`: unavailable,
  Internal Server Error; no mathematical verdict inferred from service failure.
- rg upstream Etale Derived and UpperLowerStar: found the canonical comparison and
  its natural isomorphism in UpperStarMonoidal/Comparison.lean; read the full file,
  UpperLowerStar/KFlat.lean, UpperLowerStar/FlatModuleCat.lean, Derived/Tensor.lean,
  and the exact-inverse-image identification in Derived/UpperLowerStar.lean.
- rg upstream for the item id: no hits.
- rg lean/Sheaf for the item id and pullback/tensor names: no duplicate statement;
  FiniteLisseFieldDual and EtaleFiniteTwistPullback already use this upstream iso.

Validation: scratchpad/Specialization.lean checks the actual ModuleCat specialization,
its inverse, the exact-inverse-image identification, and the dependency tensor via
scompile.py. The scratchpad is not a delivered Lean module. The delivery dry run
also checks all recorded existing declarations against the published library.

## Second reading by NZ

I independently read the node, both statement-dependency node records and their
actual declarations, Stacks sites-cohomology.tex label
lemma-pullback-tensor-product (07A4), and the upstream Comparison, Derived,
Tensor, Derived/UpperLowerStar, UpperLowerStar/Defs, Monoidal and FlatModuleCat
modules. The source assumes a morphism of ringed topoi and arbitrary objects
of the unbounded derived category; no flatness, boundedness or finiteness
hypothesis on those objects occurs. Its constant-coefficient specialization
is exactly the node. There is no statement_change or new/dependency module.

Object/hypothesis/conclusion checklist, made before assessing the Lean:

1. Schemes U,V and an arbitrary scheme morphism u:U→V. Lean has
   `{Z Y : Scheme.{u}} (g : Z ⟶ Y)`, with Z=U and Y=V. PASS: no Etale g,
   separation, nonemptiness or finiteness instance is assumed.
2. A commutative coefficient ring Λ. Specialize `A` to
   `ModuleCat.{u + 1} Λ`, with `Λ : Type (u + 1)` and `[CommRing Λ]`.
   PASS: no field, nontriviality, characteristic or coefficient flatness
   assumption. The general coefficient-category assumptions (Grothendieck
   abelian, closed symmetric monoidal, functorial flat resolutions) and
   pullback PreservesFlat are supplied by instances for modules; in
   particular FlatModuleCat supplies `upperStarPreservesFlat_moduleCat`.
3. Arbitrary K,L in D(V_et,Λ). The category is
   `DerivedCategory (Sheaf Y.smallEtaleTopology A)`, twice, in the signature
   of the two bifunctors. The objectwise `leftDerivedUpperStarTensorIso`
   explicitly binds both arbitrary objects. PASS: the derived category is
   unbounded, with no constructibility or Tor-amplitude predicate.
4. Derived tensor is the notion of def-kun-derived-tensor. Its recorded
   `Etale.derivedTensor A Y` is `curriedTensor` of the K-flat derived
   monoidal category. Both bifunctors unfold to this very tensor, on Y
   and Z respectively (read Derived.lean). PASS: no private tensor.
5. Inverse image is def-weil-pbc-inverse-image's `Etale.upperStar A g`.
   Defs.lean constructs it by sheafified left Kan extension, adjoint to
   the base-change direct image. The derived comparison uses
   `L(Etale.upperStar A g)`, identified canonically with the exact
   termwise functor `D(Etale.upperStar A g)` by
   `leftDerivedUpperStarIsoMapDerivedCategory A g`. PASS: the same
   constant-coefficient inverse image, with no assumption that g is etale.
6. The canonical map u⁻¹K ⊗ᴸ u⁻¹L → u⁻¹(K ⊗ᴸ L) is invertible.
   The recorded `leftDerivedUpperStarTensorNatIso` goes in the opposite
   direction, so take its `.symm`, or objectwise
   `(leftDerivedUpperStarTensorIso A g K L).symm`. PASS. Canonicity is
   part of the construction: `leftDerivedUpperStarTensorComparison`
   derives the ordinary oplax comparison δ, and
   `leftDerivedUpperStarTensorNatIso_hom` identifies it with the iso's hom.
   The ordinary δ is the mate of the pushforward tensor comparison
   (upperStar_δ in Monoidal.lean); its inverse is the canonical lax
   pullback comparison. Deriving it gives on K-flat representatives the
   inverse of the same degreewise comparison. This agrees with the last
   total-complex map in 07A4. The construction is not a Nonempty choice
   of an unrelated isomorphism.
7. Bifunctoriality in K,L. The iso belongs to
   `D(Y_et,A) ⥤ D(Y_et,A) ⥤ D(Z_et,A)`. PASS: naturality in both
   arguments is encoded, and preserved by `.symm`. Neither argument
   is fixed, and no quantifier is exchanged with a choice of maps.

Proof correspondence: node step 1 is the constant-coefficient sheaf inverse
image and its monoidal comparison; step 2 is the exact-derived identification
above; step 3 is the recorded tensor natural iso; step 4 is its defining
counit square and ordinary δ inverse, totalized on K-flat models. Since this
is reuse of an existing source declaration, no new theorem or docstring is
being authored and no proof is added to the stage-2 library.

Edge cases: empty schemes, zero ring, zero K or L, identity and non-etale
morphisms all satisfy the same binders; there is no Nonempty or Nontrivial
instance. Unbounded complexes and all cohomological degrees, including zero,
are included. There is no characteristic restriction or finite index set.
The size convention is the dependency's existing Scheme.{u} / ModuleCat.{u+1}
encoding: sites have object universe u+1 and morphism universe u, coefficient
module carriers have universe u+1. The arbitrary coefficient ring can be
placed in that larger universe; no equality of site object and morphism
universes has been imposed. There is no independent undersized test universe.
All scratch variables and universes are explicitly bound with autoImplicit false.

Independent searches (different words from the first worker):
- msearch leanfinder, `exact inverse image tensor product unbounded complexes
  sheaves strong monoidal`: eight hits, all ordinary sheaf/condensed monoidal
  constructions, none the required derived comparison.
- msearch loogle, `"tensor", "pullback"`: twelve hits on scheme pullback
  carrier rings and residue-field tensors, not this statement.
- msearch leansearch, `Pullback commutes with the derived tensor product of
  sheaves`: service result recorded in searches.jsonl; not used as evidence
  of absence if unavailable.
- rg of Mathlib CategoryTheory and Algebra/Homology for tensor comparison,
  monoidal pullback and derived tensor pullback: no competing declaration
  of this etale comparison.
- rg of project lean/Sheaf: EtaleFiniteTwistPullback and FiniteLisseFieldDual
  already use the same upstream objectwise iso; ringed-topos and scheme
  tensor-pullback modules concern their own coefficient constructions.
- rg/read upstream found the recorded Comparison.lean construction and its
  Derived.lean bifunctors; the upstream name index has no occurrence of the
  recorded name, so direct source reading is the evidence.

Mismatches and repairs: none. The existing declaration, signature and note
are retained verbatim; the required independent review is appended here.
Validation uses scompile.py on scratchpad/Specialization.lean, checking the
module-coefficient iso, inverse, exact-derived identification and tensor.
No delivered Lean module exists or is needed. deliver2 preflight checks the
existing-declaration record against the published library.
