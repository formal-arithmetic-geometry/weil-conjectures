## Worker report

This is a stage-2 delivery for lem-sfb-qlbar-bounded-tensor-colimit, not a second
stage-1 split. The live node has the Q13 reviewed proof split but no Lean record.
The earlier reported refusal of an unchanged node arose before a statement module
and Lean binding were supplied. This packet adds those and preserves the node's
natural-language statement and proof verbatim.

The module Sheaf.Paper.QlbarBoundedTensorColimit states bounded_tensor_colimit.
Its only postponed proof is that theorem. Its helper definitions spell out parts
of this same statement: degreewise tensor, the specified tensored cocone, the
representation/naturality clauses, and coefficient flatness. Definitions have
actual data, and the two functor-law proofs are structural proofs, not postponed
mathematical claims.

Clause-by-clause reading:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Prime ell and its fixed algebraic closure | `(ℓ : ℕ) [Fact ℓ.Prime]`; the existing PadicAlgCl and Profinite.padicAlgClRingObj use that closure. |
| Finite intermediate field E | `E : PadicAlgCl.FiniteIntermediateField ℓ`, including its subfield inclusion and finite-dimensionality. |
| Arbitrary morphism f:X to Y | `X : Scheme.{u}`, `{Y : Scheme.{u}}`, `(f : X ⟶ Y)`; no qcqs, properness or invertibility-of-ell assumption. |
| Small pro-etale sites and sufficiently large coefficients | `Scheme.ProEt.topology X` and its Y analogue; objects have universe u+1, arrows u, coefficients u+1. The tail is `AsSmall.{u+1} (Under E)`, an equivalent presentation of the ordered set of finite fields above E, in the coefficient universe. |
| R_Z, P_F,Z and B_Z | `ModuleObjectRingedComparison.ring (Profinite.continuousMapRingObj E) Z`, `QlbarInternalHom.coefficients Z ℓ E`, and `(QlbarInternalHom.coefficientCocone Z ℓ E).pt`. The latter two are the canonical scalar extensions of the regular E-module, restricted back to E. The existing coefficientModules declaration identifies these with `qlbarTailStage` and `qlbarTailVertex`, and gives the inclusion-transition and q_F equations on every section. Thus these are P_F,Z and B_Z in the fixed sectionwise equivalence, not arbitrary flat modules. |
| Finite-subextension-valued condensed Omega | The vertex uses `Profinite.padicAlgClRingObj`, whose EllAdic construction consists of continuous functions valued in one finite intermediate field. No all-continuous-functions replacement is made. |
| Actual maps q_F and inclusion transitions | `QlbarInternalHom.coefficientCocone.ι` and `QlbarInternalHom.coefficients.map`, constructed by coefficientComplexDiagram/coefficientComplexCocone with the actual mixedScalarMap of the field inclusion. The maps are not supplied as hypotheses or chosen by existence. |
| I_E small, nonempty and filtered | Its type is explicitly coefficient-small; `Nonempty (AsSmall (Under E))` and `IsFiltered (AsSmall (Under E))` are conclusions. E itself supplies the initial object. |
| Module colimit | First conjunct of `CoefficientFacts Z ℓ E`: `Nonempty (IsColimit (QlbarInternalHom.coefficientCocone Z ℓ E))`, with exactly those legs. |
| Each P_F,Z finite free | The existential natural number and isomorphism from the image of `Mod.finiteFree (padicSubfieldRingObj Z ℓ E) n` in `CoefficientFacts`. This means finite free over R_Z, not sectionwise freeness with separately chosen bases on each object. |
| P_F,Z and B_Z flat | `SheafOfModules.IsFlatOnSite` in `CoefficientFacts` for every stage and the vertex. This is the existing exact-tensor predicate, not an added assumption. |
| Canonical coefficient identifications and L exact | `IsIso (condensedPullbackHom ...)` for E, every F above E, and Omega; the displayed coefficient-change square uses the actual alpha_F, alpha_Omega and q_F. `pullback` abbreviates the existing module-object pullback transported by sectionModuleEquivalence, so its ring action is the one induced by alpha_E. `exactFunctor _ _ (pullback ...)` is a conclusion. The natural isomorphism p and vertex isomorphism b identify the finite stages and closure and satisfy the displayed equality carrying Lq_F to q_F. |
| Ordinary unbounded derived categories and standard lower bound | `DerivedCategory (Modules ...)` and `C.IsGE a`; the imported Mathlib standard t-structure is used directly. |
| Representative K with K^r=0 below a | The existential K, `Nonempty (DerivedCategory.Q.obj K ≅ C)`, and `K.IsStrictlyGE a`. The integer a is arbitrary, including negative integers. |
| Actual degreewise tensor diagram | `(tensorComplex Z ℓ E K).obj P` is `(tensorLeft P).mapHomologicalComplex (.up ℤ)` applied to K; its degree r term is P tensor K^r and differential is 1 tensor d. The map q is `NatTrans.mapHomologicalComplex ((curriedTensor _).map q)`, hence precisely q tensor 1. `tensorCocone` maps the specified coefficient cocone by this functor. |
| Represents derived tensor | `Represents` gives isomorphisms in DerivedCategory from Q of every stage complex and the vertex to the existing `siteDerivedTensorIndependentCoefficients` applied to the degree-zero coefficient and C. It also gives the commuting square for every finite-field transition and every closure leg. Derived tensor is an abbreviation for the dependency construction, not a second tensor definition. |
| Same strict bound for all M_F and their colimit | The universal stage `IsStrictlyGE a` and the vertex `IsStrictlyGE a` in the X clause. |
| Termwise colimit | First conjunct of `Represents`: for every degree r the evaluation of the tensor cocone is IsColimit. Its vertex is B tensor K degreewise and legs are q_F tensor 1. |
| Every A on Y and every representative J | The last universal clause quantifies over arbitrary unbounded A and J and only assumes `Nonempty (Q.obj J ≅ A)`. No K-flatness, lower bound or constructibility is imposed. `Represents Y ℓ E A J` supplies the termwise colimit and its derived representation. |
| The cohomology map induced by those legs is an isomorphism | For every integer q, the cocone obtained by `DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor _ q` from `tensorCocone Y ℓ E J` is IsColimit. This states exactly that the canonical map from the colimit of its H^q stages to H^q of its specified vertex is an isomorphism. Its legs are literally H^q(Q(q_F tensor 1)); an unspecified isomorphism between unrelated objects would not suffice. The derived-representation leg squares identify these with the derived coefficient legs in the node's formula. |

Dependency declarations read and used:

- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses:
  SheafOfModules.cochainModulesMonoidal and its preadditivity/tensor instances.
- Mathlib.Algebra.Homology.DerivedCategory.TStructure:
  DerivedCategory.TStructure.t, IsGE and isGE_iff; strict lower bounds are
  CochainComplex.IsStrictlyGE.
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence:
  CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence and
  sectionRingSheaf, retaining underlying sections and additive maps.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology.
  Scheme and size convention nodes introduce no substitute definitions.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  coefficientRing and condensedRingObj, the actual inverse image from the point.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients:
  coefficientMap and map_coefficientMap_comp_condensedPullbackHom.
- WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic:
  Profinite.padicAlgClCondensedRing/padicAlgClRingObj, finite-subextension-valued.
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions: the recorded
  unbounded derived convention; actual categories here are Mathlib DerivedCategory.
- Sheaf.Paper.QlbarInternalHomCoefficientComparison:
  QlbarInternalHom.fields, coefficients and coefficientCocone only.
  These plain constructions are now owned by the new definition node
  def-sfb-qlbar-coefficient-module-cocone. No theorem from that module is
  used in the signature; its internal-Hom theorem node is removed from stmt_deps.
- Sheaf.Paper.InternalSectionTotalComparison: ModuleObjectRingedComparison.ring,
  Modules, equivalence and its Grothendieck/derived-category instances; its
  owning definition node is added to stmt_deps.
- Sheaf.Paper.QlbarTailModuleColimit: no declaration from this module is used
  in the signature. The tail-module colimit theorem node is removed from
  stmt_deps. qlbarTailStage/Vertex are only explanatory comparisons, owned by
  def-sfb-qlbar-tail-module-objects, so that definition is not added either.
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients:
  siteDerivedTensorIndependentCoefficients, the recorded canonical K-flat
  localization. This existing node is added to stmt_deps for the functor used
  in the signature.

The module imports the available proof-dependency modules for filtered-colimit
flatness, tensor preservation of colimits, K-flat resolutions, truncations,
Cartesian coefficients, exact forgetful functor and exact filtered colimits of
abelian sheaves, and homology of exact functors. The two as-yet-unbound proof
nodes (flat single-coefficient tensor and tail finite-free algebra presentation)
introduce no objects needed to elaborate the signature, so no replacement
statements are invented for them in this delivery.

Edge cases checked: F=E is included in Under E and gives the rank-one coefficient;
there is no empty-index hypothesis hidden in the statement. Zero complexes and
the empty scheme remain allowed. Both a and q range over all integers. K can be
unbounded above, and J is arbitrary in both directions. Characteristic ell is
allowed: untwisted Cartesian coefficients do not require ell invertible.
The sites retain distinct object and morphism universes. The entire derived
representation is stated by derived isomorphisms, with a separate homology
colimit clause, following the 2026-10-21 isomorphism convention.

Searches made with the required msearch wrapper (recorded in searches.jsonl):

- LeanFinder, "Finite subextension coefficient sheaves tensor bounded below
  complex filtered colimit cohomology": eight results concerning sheaf cohomology,
  local cohomology and finite presentation; none states this coefficient result.
- Loogle, `"SheafOfModules", "tensor"`: ten results concerning the ordinary
  presheaf tensor and its colimit preservation; no matching theorem.
- Grep, `filtered.*tensor|tensor.*filtered` in Algebra/Category/ModuleCat/Sheaf:
  zero results.
- Project rg in WeilConjectures and Sheaf for the item identifier: no matching
  existing declaration. Searches for qlbar, finiteSubextension, tail modules and
  finite freeness found QlbarTailModuleColimit and the existing normalized
  coefficient diagram, which are reused. No full duplicate statement was found.

The node's statement needs no correction. No STATEMENT-DISPUTED issue was found.
The added statement dependencies were checked for paths back to this item; none
creates a cycle. No source repository edits, direct Git commands, global builds,
launcher changes or other-agent work were used. All compilation uses scompile.py.


## New nodes

def-sfb-qlbar-coefficient-module-cocone owns the existing declarations
`AlgebraicGeometry.ProEtale.QlbarInternalHom.fields`, `coefficients`, and
`coefficientCocone` in `Sheaf.Paper.QlbarInternalHomCoefficientComparison`.
Its `existing: true` record retains the sole implementations in N8's landed
module. The definition states the small tail projection, the scalar-extension
complex diagram of the degree-zero regular E-module followed by complexForward
and evaluation at zero, and the image of its actual closure cocone. It makes no
colimit, finite-free, flatness or internal-Hom assertion. This is the coefficient
union construction preceding HRS Lemma 5.6. The general complex diagram and the
fixed section equivalence have their own definition owners, cited by this node.
The existing restricted-regular-object node does not define this diagram or its
maps. No prior definition node owns these three specialized declarations.

Searches for this owner: LeanSearch's finite-intermediate-field coefficient module
query returned eight general module-colimit and intermediate-field facts;
Loogle `Cocone, Under, ModuleCat` returned no hits (unknown identifier `Cocone`);
The corrected Loogle name query `"Cocone", "ModuleCat"` returned twelve
general module colimit/coproduct cocone declarations, with no exact match.
Mathlib grep for coefficientComplexDiagram/QlbarInternalHom/coefficientCocone
returned zero hits. Project grep found the three existing plain definitions and
the general complex construction, with no upstream WeilConjectures counterpart.
Definition-node grep found no owner; blueprint_refs search found 27 broader
coefficient-module hits, none owning these declarations. Exact wrapper outputs
are preserved in the new node's mathlib_searches and searches.jsonl.

## Returned-delivery repair and self-check

The initial saved-packet dry run passed at 6cb7bc28a07. The return on immutable
head cb44c158f32b nevertheless identifies two dependency ownership faults, both
repaired here rather than re-pushing that unchanged packet:

1. Replace the internal-Hom coefficient comparison theorem in stmt_deps by the
   new existing-definition owner above. Reading lines 172-205 shows that fields,
   coefficients and coefficientCocone are plain constructions. No internal-Hom
   theorem is called in the tensor statement or any of its helper definitions.
2. Remove lem-sfb-qlbar-tail-module-colimit from stmt_deps. Neither its theorem
   nor qlbarTailStage/Vertex occurs in the delivered Lean file. The report's
   comparison to those objects explains the coefficients but is not a signature
   dependency. There is therefore no need to add their definition owner.
3. Keep lem-weil-pbc-site-derived-tensor-descent: derivedTensor really uses
   siteDerivedTensorIndependentCoefficients, obtained from that theorem's
   determining construction, as the return already confirmed.

The saved packet differs from current main only by the intended item lean record
and added statement dependencies. The returned theorem module is retained
verbatim: no mathematical statement, hypothesis, universe, helper data or proof
has changed. The new node's three signatures/bodies were read directly in N8's
landed module. Its primary signature is copied verbatim. Its statement describes
that construction, including both actual under-category inclusions and the
actual cocone legs. Its base E remains an index; zero and empty-scheme cases
remain allowed. Ownership is metadata, with no extra Lean declaration or axiom.
The clause-by-clause table above and the maintainer's returned clause audit remain
applicable to the unchanged theorem. This is the worker's self-check; the
maintainer performs the independent delivery review.


Validation: explicit scompile.py passed for the retained tensor module (sandbox
36.1 s, library 19.1 s). The repaired packet dry run passed at ca4a72ca33e,
including compilation of the existing-definition ownership check. Local metadata
self-check confirms exact signature transcription, citation/dependency equality
for the new node, and no statement-dependency cycle from either delivered node.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
