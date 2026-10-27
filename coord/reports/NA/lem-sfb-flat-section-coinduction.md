## Worker report

Stage 2 handoff: the live item is already split and reviewed by NS/L on 2026-10-23;
there is no released repair note. The sandbox had no prior module, node copy, report,
compiler process or delivery in this session. I preserved that accepted statement and proof.
The stage-2 instruction supersedes the old stage-1-only task. No live file was written.

Files: lean/Sheaf/AlgebraicGeometry/FlatSectionCoinduction.lean and the item's node copy.
No new DAG nodes or dependency modules. The main declaration is
AlgebraicGeometry.exists_flatSectionCoinduction, with sorry as its only proof.
The auxiliary abbreviations and definitions construct parts of the same coinduction notion;
none chooses unspecified data from an unproved existence statement.

Hypotheses: Z,W : Scheme, CompactSpace and QuasiSeparatedSpace on both, p : W → Z
with Flat p and LocallyOfFinitePresentation p, i : Z → W with IsClosedImmersion i,
and hi : i ≫ p = identity. The localization universe of Z and W is independent.
The shared HasDerivedCategory binders are for SheafOfModules (moduleRings X.toRingedSpace),
not a second derived category on the Scheme.Modules category instance.
c is supplied between schemeDerivedQCohCategory W and schemeDerivedQCohCategory Z;
adj has left functor flatSectionQCohPushforward i, constructed by lifting the canonical
schemeDerivedDirectImage i. The supplied M is in D_QCoh, with boundedness exactly
∃ n : ℤ, M.obj.IsGE n (equivalent to H^j=0 for j<n).

Conclusion: Φ is a family of actual isomorphisms Ri_*c(M) ≅ RHom(B,M).
The first conjunct is naturality for every derived morphism between bounded-below
quasi-coherent objects. The second uncurries Φ by schemeDerivedTensorHomEquiv and
precomposes with identity tensor the algebra unit. The result equals the right unitor
(after identifying O_W[0] with the tensor unit) followed by adj.counit. Thus it is exactly
evaluation at the unit. The third conjunct quantifies over every h : O_Z[0] → c(M).
flatSectionPushforwardStructureIso.inv identifies B[0] with Ri_*O_Z[0]; hence the right side
is m followed by ξ, and the left side is the canonical tensor-Hom image of Φ Ri_*h.
This explicitly fixes the order of both tensor factors and the direction of every comparison.

Canonical maps: flatSectionAlgebraModule is ordinary SheafOfModules.pushforward of unit;
flatSectionAlgebraUnit is DerivedCategory.singleFunctor.map of unitToPushforwardObjUnit.
flatSectionOrdinaryMultiplication takes the first multiplication witness of the existing
moduleBaseChangeMap_algebra on the identity square. Its sectionwise product condition
uniquely fixes this morphism (tensor universal property), so this is not arbitrary algebra data.
flatSectionTensorSingleIso uses the standard mapBifunctorSingle₁Iso and singleMapHomologicalComplex.
flatSectionDerivedMultiplication is the canonical pullbackTensorModelMap followed by Q of
ordinary multiplication, conjugated by singleFunctorIsoCompQ. It does not assume B flat.
flatSectionStructureUnitIso uses DerivedCategory.singleFunctorObjUnitIso with the shared
scheme tensor construction. flatSectionPushforwardStructureIso uses exactness of closed
pushforward and Functor.singleFunctorCompRightDerivedFunctorIso, not an arbitrary chosen iso.

Dependency interfaces read: WeilConjectures.AlgebraicGeometry.DerivedCategory
(schemeDerivedCategory, schemeDerivedQCohCategory, schemeDerivedQCohProperty);
SchemeDerivedDirectImage (schemeDerivedDirectImage); DerivedTensorStructure
(schemeDerivedTensorMonoidal); CanonicalDerivedTensorHom (schemeDerivedTensorHomEquiv);
CanonicalPullbackTensorComparison (pullbackTensorTotal, pullbackTensorModelMap);
ClosedModulePushforwardHomology (closed_modulePushforward_preservesHomology);
ModuleBaseChangeMapAlgebra (Scheme.Modules.moduleBaseChangeMap_algebra).
The current def-pur-derived-internal-hom module publicly reexports the original generic
CategoryTheory.derivedInternalHom; the ordinary-module presentation is not applied to schemes.
The generic declaration and its K-injective construction were read directly.
The three additional stmt_deps are already landed nodes for these canonical maps/lifts;
no existing dependency record is replaced. All published proof-dependency modules are imported
with plain import; the three currently unstated pseudo-coherence proof prerequisites are omitted.

Sources read: duality.tex lemma-sheaf-with-exact-support-adjoint (0A76),
lemma-sheaf-with-exact-support-ext (0A77), lemma-twisted-inverse-image-closed (0A9X),
and the trace-closed-immersion paragraph. The stage-1 proof is copied into the main
declaration's docstring in eight steps, including the algebra-action and K-flat calculation.
No Noetherianity, properness of p, or perfection of B is inserted.

Existing-declaration search: rg by blueprint id and flatSectionCoinduction/flat_section_coinduction
in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no declaration.
The earlier coinduction keyword search found discrete representation coinduction and ordinary
sheaf coinduction, which do not state this derived comparison or its normalization.
Mathlib searches were executed with msearch.py and logged in searches.jsonl:
- leanfinder: "For a closed immersion of schemes the right adjoint to derived pushforward on quasi coherent complexes has pushforward given by derived internal Hom from the closed subscheme structure sheaf".
- leanfinder: "Derived sheaf coinduction for a closed subscheme equals RHom from its direct image algebra with multiplication action and evaluation counit".
- leansearch: "For a closed immersion of schemes the pushforward of its derived right adjoint on bounded below quasi coherent complexes is derived sheaf Hom from the structure algebra, with evaluation counit".
- loogle: "CategoryTheory.Adjunction, CategoryTheory.DerivedCategory" (unknown second identifier; not evidence of absence).
- loogle: "CategoryTheory.Adjunction, DerivedCategory" (no hits).
- grep: "coinduct|twistedInverse|derived.*[Ii]nternal[Hh]om" in AlgebraicGeometry (no hits).
The semantic hits give ordinary pullback/pushforward and open restriction adjunctions,
not this statement. unitToPushforwardObjUnit was a useful existing canonical-map hit.

Edge cases: identity section gives the unit algebra, arbitrary M remains allowed;
M=0 and empty schemes require no nonemptiness binder. For a flat thickening over a field,
Z=Spec k → Spec(k[ε]/ε²), B need not be perfect: multiplication is still the derived
multiplication induced from ordinary multiplication, and no Tor vanishing is imposed.
The lower bound is existential, not fixed globally. Naturality allows two different lower
bounds. All h are ambient derived maps from O_Z, with no artificial boundedness assumption
on c(M). The image of c(M) is quasi-coherent by its codomain.

Validation: compiler initially rejected a namespace qualification and arrow-to-isomorphism
parsing in the existential family; both were corrected. The complete module then compiled
cleanly in sandbox mode and its actual library module mode. The final delivery dry run
also validates the required proof imports and record. No Lean theorem was proved.

## Second reading by NA

This direct-delivery session has no second worker; this is my separate rereading of the
completed signature against the accepted node, not a claim of an independent agent review.
I checked each binder against the first sentence: qcqs schemes, flat lfp p, closed section
with i ≫ p = id, and the supplied right adjunction on the full quasi-coherent categories.
I traced the endpoints of every equation: the evaluation equation starts at
Ri_*c(M) tensor O_W[0], while the final equation starts at B tensor B. The exact comparison
has direction Ri_*O_Z → B; its inverse is therefore the arrow needed before Ri_*h.
The tensor-Hom bijection is the recorded canonical bijection, not a fresh adjunction.
I checked that Φ is a single family natural in M, rather than separate unrelated choices.
The lower-bound witness is proof-irrelevant and leaves all bounded-below inputs available.
The second equation matches ε_M; the third matches m ≫ ξ exactly, with no sign from
the degree-zero algebra. The ordinary multiplication witness is fixed on all local pure
tensors by the cited existing theorem and therefore determined by sheafification.
I reread the generic RHom module reexport to ensure that the new ordinary-module
abbreviation had not changed the sheaf endpoint. No mathematical mismatch required
changing the accepted statement. The final check is the compiler and preflight, followed
by the maintainer's independent review of this delivered packet.
