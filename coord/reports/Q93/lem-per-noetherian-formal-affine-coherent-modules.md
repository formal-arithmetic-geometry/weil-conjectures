## Worker report

Item: lem-per-noetherian-formal-affine-coherent-modules. Group Q93, 2026-10-24.

The module `Sheaf.AlgebraicGeometry.NoetherianFormalAffineCoherentModules` states
`AlgebraicGeometry.noetherianFormalAffine_coherentModules`, with one postponed proof.
All seven helper definitions contain actual data, using existing category, sheaf,
quotient, tilde, evaluation, or pullback constructions. No theorem is used to choose
an unspecified sheaf, equivalence, tensor map, or inverse functor. The equivalence
and its comparisons remain existentially quantified in the theorem.

The original statement, proof and proof dependencies are unchanged. The only extra
statement dependency is the already landed `def-per-adic-principal-chart-data`,
which owns the canonical map Spf -> Spec, principal opens, and R-action on sections.
No dependency repair, statement correction or new definition node is needed.

### Hypotheses and objects

- A commutative ring: `R : CommRingCat.{u}`; its commutative-ring instance is bundled.
- Noetherian: `[IsNoetherianRing R]`, the exact declaration in the dependency record.
- A finitely generated ideal: `(K : Ideal R) (_hK : K.FG)`. The explicit finite-generation
  hypothesis is retained even though Noetherianity also supplies it.
- The compatible-residue ring map is an isomorphism: `[IsAdicComplete K R]`. This is
  the recorded Mathlib predicate, equivalent to bijectivity of `AdicCompletion.of`.
- The ringed space T is the recorded `adicFormalSpec R K`, not an ordinary scheme
  or a substitute inverse-system category. Its definition is the ringed-space
  colimit of the canonical thickenings. The published principal-chart theorem
  identifies its space with V(K) and its ring sheaf with the quotient inverse limit.
- Finite modules and their R-linear maps: the full subcategory
  `ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} R ↦ Module.Finite R M)`.
  Full-subcategory morphisms have exactly the underlying `ModuleCat` linear map.
- Coherent O_T-modules and module maps: the full subcategory of
  `RingedSpace.IsCoherent (adicFormalSpec R K)`. This predicate is exactly finite
  type plus finite-type kernels for all maps from finite free modules on all opens.
  The repaired pqf-def-coherent module exposes this recorded upstream predicate.

### Each conclusion and its Lean rendering

1. The completed associated sheaf M-triangle is specified by `p M s`, a cone over
   `adicModuleQuotientSections R K M.obj s`, together with
   `Nonempty (IsLimit (Cone.mk _ (p M s)))` for every principal open. Its n-th term
   is the sections on D(s) of `tilde (M/K^(n+1)M)`, regarded as an R-module sheaf
   on Spec R. The recorded tilde localization instance identifies this with
   `(M/K^(n+1)M)_s`. This uses positive powers, with Lean index n representing n+1.
   The quotient transitions are `AdicCompletion.transitionMap`, transported by
   `tilde.functor`, so the diagram is the actual quotient-localization diagram.
   Closed pushforward from Spec(R/K^(n+1)) gives this same tilde sheaf on Spec R;
   it is supported on V(K). Evaluating it on D(s) therefore computes its value
   on D(s) intersect V(K). Principal opens form a basis, so the compatible limiting
   cones characterize the sheaf inverse limit in the statement.
2. The O_T-action is also fixed: the first natural isomorphism identifies the
   underlying forward functor with `tilde.functor R ⋙ adicFormalModulePullback R K`.
   This helper specializes Mathlib's existing module pullback along the recorded
   `adicFormalSpecToSpec`. For finite modules, a finite presentation gives the
   cokernel of the same matrix over O_T for both this pullback and the completed
   associated sheaf (node steps 2, 5 and 6). This is an equivalent construction of
   the node's M-triangle, not an additional assumption or a replacement of it.
   It prevents the R-module limiting cones from leaving the sheaf scalar action
   implicit. All actual tensor products are the shared sheaf or module tensors.
3. Exact equivalence: the existential `E : finite modules ≌ coherent modules`, with
   `PreservesFiniteLimits E.functor ∧ PreservesFiniteColimits E.functor`. These are
   exactness in the finite-module/coherent categories, not a claim about each
   individual quotient functor. All functor maps are genuine module maps.
4. Global-section quasi-inverse: `γ` is the natural isomorphism from E.inverse,
   after forgetting finite generation, to the global-section functor. The latter
   is `adicFormalModuleSections R K ⊤`, with R acting by the canonical global ring
   map `adicFormalGlobalSection R K`. Thus the inverse is global sections on both
   objects and morphisms, up to the usual canonical natural identification.
5. The unit is `η`, and the equation
   `η.hom.app M = (E.unitIso.hom.app M).hom ≫ γ.hom.app (E.functor.obj M)`
   identifies it with the unit of this equivalence, under γ. The formula for
   `(p M s).app (op n)` on `adicFormalModuleUnitSection ... m` is precisely the
   residue of m, followed by `tilde.toOpen`. At s=1 this is the compatible-residue
   global map, so it is the unit required in the node, not an arbitrary unit iso.
6. R-triangle -> O_T: the displayed sheaf isomorphism `e` has source E(R), target
   `SheafOfModules.unit (moduleRings T)`, and sends the unit image of r to
   `adicFormalGlobalSection R K r`. It is an O-linear morphism, so normalization
   on r=1 fixes multiplication by all local structure-sheaf sections.
7. Tensor compatibility: `μ` is an isomorphism from
   `SheafOfModules.siteSheafTensorRight Ntriangle` applied to Mtriangle to the
   forward image of `ModuleCat.of R (M ⊗[R] N)`. Its section formula for every
   open U sends `siteSheafTensorTmul` of the sections from m,n to the section from
   `m ⊗ₜ[R] n`. These are the canonical coefficient-multiplication formulas; the
   maps are O-linear sheaf morphisms, so they also determine their action on local
   scalar multiples. Finite-presentation generation fixes the comparisons
   uniquely, hence gives their naturality in both module variables.
8. Sections on every D(s) intersect V(K): the limiting-cone clause in (1) is exactly
   an identification with the inverse limit, including the coordinate maps. It is
   stronger as an interface than a bare `Nonempty` isomorphism of section modules:
   the isomorphism to the chosen limit is determined by the cone projections.
9. Canonical quotient-localization restrictions: the next-to-last clause equates
   residue after the actual sheaf restriction to D(st) with restriction of the
   quotient tilde section from D(s) to D(st). Both maps use `homOfLE` of the actual
   open inclusions. These product restrictions determine arbitrary inclusions of
   principal opens: when D(t) is contained in D(s), D(st)=D(t), so sheaf transport
   supplies the same restriction. The formulation quantifies over every proof of
   the formal principal-open containment and adds no geometric hypothesis.
10. Naturality in module maps: the last clause equates each residue of E(f)(x)
    with the tilde map of `f.hom.hom.reduceModIdeal (K ^ (n+1))` on the residue
    of x, for all local x and every level. The inverse-section comparison γ and
    the unit η are natural isomorphisms, so object and morphism identifications
    agree on global sections as well.

### Dependency declarations read and used

Each original statement-dependency node was read, including its complete statement
and Lean/mathlib record; the owning source declarations and docstrings were opened.
The extra landed dependency was also read in full.

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finitely generated).
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, `IsAdicComplete`, and
  `AdicCompletion.transitionMap`; the n=0 quotient is zero, hence harmless to omit.
- `Sheaf.AlgebraicGeometry.AdicFormalGeometry`: `adicFormalCompletion`, `adicFormalSpec`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde`, `tilde.functor`, `modulesSpecToSheaf`,
  `tilde.toOpen`, `tilde.toOpen_res`, and the `IsLocalizedModule.Away` instance.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, publicly exposing
  `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`, alongside
  Mathlib's finite-type and quasicoherent predicates. The scheme-specific conjunction
  is not substituted for the actual ringed-space coherence predicate.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, through its public
  `SiteTensorFunctoriality`/`TensorProductOfUniverses` imports:
  `SheafOfModules.siteSheafTensorRight`, `siteSheafTensorTmul`. Their definitions are
  sheafification of the sectionwise tensor, and its sheafification-unit pure tensors.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: ordinary `TensorProduct`, pure tensors,
  and extension of scalars. The dependency's `LinearMap.baseChange` and
  `TensorProduct.AlgebraTensorModule.distribBaseChange` signatures/docstrings were read;
  this item needs the ordinary tensor object, not an extra base-change functor.
- `Mathlib.CategoryTheory.Limits.HasLimits`: limiting cones `IsLimit`, equivalently
  the recorded `limit`/`limit.π` with their canonical projection comparison.
- `Sheaf.AlgebraicGeometry.AdicPrincipalChartData`: `adicFormalSpecToSpec`,
  `adicFormalPrincipalOpen`, `adicFormalGlobalSection`. The complete module was read.

The seven helpers specialize the above or existing Mathlib APIs:
`SheafOfModules.forgetToSheafModuleCat`, `sheafCompose`,
`SheafOfModules.pullback`, `TopCat.Sheaf.forget`, categorical evaluation,
`Functor.ofOpSequence`, and restriction maps. Their data contain no `sorry`.
Their docstrings carry this item's source and blueprint id. These helpers are
part of the single completed-associated-module notion, not new independent notions.

All recorded, stated proof-dependency modules are imported plainly (not publicly)
as required by the stage-2 contract. This includes completion exactness and tensor
comparison, finite-module completeness, coherent-kernel/cokernel closure, the affine
quotient-system equivalence, closed pushforward, principal-chart refinement, and
ordinary sheaf-tensor colimit preservation. Mathlib proof leaves are imported from
the files in their `mathlib_match`. No duplicate Sheaf version of an upstream module
is imported. The theorem docstring includes all eleven natural-language proof steps.

### Edge cases checked before writing

- K=0: positive quotients are M, the formal spectrum is Spec R, and the theorem
  reduces to the usual affine coherent/finite-module correspondence.
- K=R: completeness and separatedness force R to be the zero ring. V(K) is empty,
  and both categories contain only zero modules up to isomorphism. No Nontrivial
  assumption or nonempty-space hypothesis excludes this case.
- R the zero ring, zero modules, rank-zero presentations and zero tensor factors
  are allowed. `Module.Finite` is finite generation, not finiteness of the set.
- s=0 gives the empty principal open and zero localized quotient sections; s=1
  gives all of T and identifies η with the global compatible-residue map.
- R=k[[t]], K=(t): only unit s give nonempty formal principal opens, as expected.
- Quotients use n+1, so no unwanted condition from the empty zeroth thickening is
  imposed. The existing formal-spectrum definition includes that initial empty
  term, which does not change its colimit.
- No field, local-ring, reducedness, characteristic, or algebraic finite-type
  assumption is introduced. All universes and variables are explicitly bound;
  `autoImplicit` is false. Finite modules over a Type-u ring have Type-u models,
  so the category representatives do not omit a mathematical finite module.

### Searches

Prescribed wrapper searches, recorded in the sandbox's `searches.jsonl`:

- LeanFinder: "Finite modules over a complete Noetherian adic ring are equivalent
  to coherent sheaves on its formal spectrum". Eight hits: seven adic completion,
  tensor/completeness facts and `AdicCompletion.map_injective`; none is the formal
  coherent-module equivalence. Read the relevant completion interfaces.
- Loogle: `"FormalScheme", "Coherent"`: zero hits.
- Mathlib grep wrapper: `FormalScheme|Spf|completedAssociated` in AlgebraicGeometry:
  zero hits.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for `adicFormalSpec`,
  `adicFormalCompletion`, completed-associated/tilde names and formal affine module
  phrases: found the actual formal-spectrum/chart definitions and the ordinary
  scheme quotient-system equivalence, but no sheaf-on-Spf version of this theorem.
- Exact blueprint-id search in `lean/WeilConjectures`: no hit. Searches for all
  eight proposed declaration names in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json`: no clash.
- DAG/source searches distinguish `lem-weil-pbc-coherent-formal-modules-affine`
  (087W: quotient systems on the ordinary Spec) from this item's module sheaves
  on Spf. The former is a proof dependency, not an existing exact match.

Source read: local Stacks `formal-spaces.tex`, section-formal-schemes-EGA (0AHY),
including the common quotient-spectrum space, inverse-limit ring sheaf and
completed-localization formula; `modules.tex`, definition-coherent (01BV);
the current blueprint's ancestor affine-curve statement. The node itself records
that archival EGA I is WANTED; this delivery does not pretend to have read it or
change its source attribution.

Validation: prescribed `scompile.py` compiled the sandbox and final module cleanly
against the live published library. Maximum line width is 95. No statement dispute,
missing interface, extra axiom, data-valued sorry or node-statement fault was found.

## Second reading by Q93

A separate second pass by this worker reopened the node and final file and checked
all hypotheses and all ten conclusion mappings above. The explicit ringed-space
coherence predicate agrees with 01BV, rather than the scheme-only quasicoherent
finite-type conjunction. The positive quotient tower, its actual linear transitions,
limiting cones, residue normalization of η, γ global-section inverse, tensor pure
formula, restriction and module-map compatibility were all checked in the final
signature. The finite-presentation pullback characterization fixes the O-action;
it introduces no assumption and follows from exactly the same matrix construction
as the source's completed associated sheaf. No mathematical clause changed on this
pass. Compiler repairs fixed only an open-map composition, functor inference and a
line break. This worker has not represented this self-check as an independent
agent review: the dispatcher brief forbids starting other agents and assigns the
independent review to the maintainer after delivery.
