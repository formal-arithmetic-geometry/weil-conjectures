## Worker report

This is stage 2, not a second split of the reviewed stage-1 node. The preserved sandbox
contained only dispatcher retry markers. No reviewed split, proof route, unit statement,
or natural-language item statement is changed. The delivery states
`AlgebraicGeometry.KummerLine.kummer_affine_line` and supplies the missing module-coefficient
specialization in `Sheaf.AlgebraicGeometry.KummerModuleCoefficients`. All four theorems have
`sorry` proofs and source/proof docstrings. All definitions have actual data. The two scalar
instances use Mathlib's uniquely determined residue-ring action, not a choice of module data.

The item is read against the reviewed DAG statement and the original blueprint item and unit,
read on the server at `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/`.
The original blueprint's rank-one and “finite A-modules” wording was already repaired by the
reviewed stage-1 split; this delivery retains that repaired statement verbatim.

Clause-by-clause correspondence:

- `k : Type u`, `[Field k]`, `[IsAlgClosed k]` render the algebraically closed field. `ℓ N : ℕ`,
  `hℓ : ℓ.Prime`, `hℓk : IsUnit (ℓ : k)` and `hN : 1 ≤ N` render precisely the prime,
  invertibility, and positive-exponent assumptions. Every occurrence of m is `ℓ ^ N`.
- R is `ULift.{u+1} (ZMod (ℓ^N))`, canonically isomorphic to Z/m. The lift is needed because
  the existing monoidal and sheafification APIs use a coefficient ring in the module universe.
  It imposes no equality of independent universes and excludes no finite module: every finite
  R-module has a representative in `Type (u+1)`. Scalars are transported by `ULift.ringEquiv`.
- `A : ModuleCat.{u+1} R` with `Module.Free R A` and `Module.Finite R A` is a finite free
  R-module of arbitrary rank r, including r=0. A basis is not chosen or added as a hypothesis.
- `curve k false` is literally `Spec (CommRingCat.of (Polynomial k))` and `curve k true`
  literally `Spec (CommRingCat.of (LaurentPolynomial k))`. Their structure maps are induced
  by the canonical scalar inclusions. `inclusion k` is `Spec.map Polynomial.toLaurent`.
  Their being smooth affine connected curves is a fact used in the proof, not an assumption
  imposed on otherwise unspecified schemes.
- `Scheme.rootsOfUnitySheaf m` is the existing kernel of the m-power map on G_m, with the
  existing exponent module presheaf `finiteEtaleMuModulePresheaf`. No second root sheaf.
  The new `kummerModuleTwist` sheafifies its tensor with the constant module presheaf A.
  Since tensor preserves sheafification equivalences, this is precisely μ_m tensor A_C.
  `kummerAbelianTwist` only forgets the module structure for the existing `Sheaf.H` API.
- `ζ : kˣ`, `hζ : IsPrimitiveRoot ζ (ℓ^N)` is the primitive root choice. For m>0, a primitive
  root in k is a unit, so bundling it as a unit adds no assumption. The existential family
  `z b` is in H⁰(C,μ_m). Its first conjunct says that after the actual H⁰/sections equivalence
  and kernel inclusion it is the scalar ζ. The inclusion is injective, so this specifies the
  section uniquely. Its coefficient image is literally the constant section ζ tensor a.
- The H⁰ equivalences are `e : A ≃ₗ[R] Sheaf.H (kummerAbelianTwist C m |>.obj A) 0` with
  `e a = Sheaf.H.map (kummerCoefficientInsertion C m A a) 0 (z b)`. This explicitly fixes
  their direction and their action, not merely the abstract isomorphism types.
- The vanishing clause uses `(if b then 1 else 0) < q`: q>0 for the affine line, q>1 for the
  punctured line. `Subsingleton` is vanishing of the actual abelian group `Sheaf.H F q`.
- `generator k m hm` is the existing `kummerδ₀` applied to the coordinate unit t. That unit
  is the image of `LaurentPolynomial.T 1` under `ΓSpecIso.inv`; its inverse is T^(-1).
  The existential proof `hm : IsUnit (m : Γ(G_m,⊤))` is a conclusion, not an extra hypothesis.
  The degree-one equivalence sends a to `H.map i_a 1 (generator k m hm)`, as required. Taking
  A=R and a=1 identifies its image with κ_m(t) under the canonical μ_m tensor R=μ_m map.
  An R-linear equivalence with A says exactly that this group is free of rank r; separate
  freeness and rank conjuncts would repeat a consequence of the displayed equivalence.
- `rootRestriction` is the actual `Etale.cohomologyMap` composed with the canonical
  `upperStarRootsOfUnitySheafToRootsOfUnitySheaf`. The theorem asserts it takes `z false`
  to `z true`. Restriction with coefficients is uniquely characterized, for every x and a,
  by `res (H⁰(i_a)(x)) = H⁰(i_a)(rootRestriction x)`. This is the tensor naturality
  characterization of the actual restriction, not a free choice of map. The coefficient
  comparison is an isomorphism and its pure tensors generate, so this characterization
  determines it uniquely. The last conjunct explicitly says it carries ζ tensor a to
  ζ tensor a, i.e. is the identity of A in the displayed degree-zero coordinates.
- `∀ q, Finite (Sheaf.H ... q)` renders finiteness of every cohomology group. The helper's
  global residue-ring instances make these groups actual R-modules; hence they are finite
  R-modules, not just unstructured finite types.
- For each curve and q the coefficient comparison is an R-linear equivalence whose value
  on `x ⊗ₜ a` is exactly `Sheaf.H.map i_a q x`. Its formula determines the map uniquely.
- For each finite free B and linear f, the explicit equality
  `H.map (kummerAbelianTwist.map f) q (H.map i_a q x) = H.map i_(f a) q x`
  renders naturality. Substituting z gives naturality of H⁰ sections, and substituting
  κ_m(t) gives naturality of the H¹ identifications. The coefficient-comparison square
  commutes because its pure tensors generate its domain.
- The last clause in the coefficient block quantifies over commutative R-algebras S which
  are finite free as R-modules. Its equivalence has source H^q(C,A(1)) tensor_R S and target
  H^q(C,μ_m tensor_R (A tensor_R S)). The formula for all x,a,s is exactly
  H^q(i_a)(x) tensor s mapping to H^q(i_(a tensor s))(x). In particular x=κ_m(t) is the
  displayed Kummer compatibility. This formula also determines the scalar-extension map
  uniquely, and identifies its S-action with the action on the S tensor factor.

Dependency declarations used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve` and its connected
  curve convention, read with its full docstring. The literal spectra above fix the curves.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: `Scheme.kummerSequence`,
  `Scheme.rootsOfUnitySheaf`, `Scheme.kummerδ₀`, and `Scheme.kummerSequence_shortExact`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale` and `Scheme.smallEtaleTopology`.
- The recorded etale-cohomology node explicitly permits the source's `CategoryTheory.Sheaf.H`
  encoding, used by `kummerδ₀`; its bridge with `Etale.cohomology` is stage 3. No duplicate
  derived cohomology functor is defined here.
- The recorded etale-sheaf node supplies `Sheaf`, `constantSheaf`, and the module-valued
  sheaf encoding. Its source predicate `Scheme.IsLocallyConstantEtaleSheafOfSets` was also
  read; no local-constancy hypothesis or copy of that predicate is introduced.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`: `finiteEtaleMuModulePresheaf` and
  `finiteEtaleMuModuleObj` (via the presheaf), with its exponent action. This is an added
  dependency through the new definition node. The older ring-coefficient `finiteEtaleTateLine`
  is not usable for an arbitrary module A and is not copied.
- `def-pur-sheaf-tensor-product` records the site-universe-general sheafified tensor of modules
  over a ring sheaf. The module-valued sheaf encoding here uses the same sectionwise Mathlib
  `TensorProduct` and `presheafToSheaf` specialization, already used by the finite Tate module;
  no alternate tensor or scalar-extension operation is introduced. Its recorded module is
  imported, along with the general-site tensor construction imported by the finite Tate module.
- `WeilConjectures.EtaleCohomology.TateTwist.Sheaf` supplies the canonical roots pullback
  comparison; `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
  supplies the canonical `Etale.cohomologyMap`.
- Proof-only imports include the recorded affine cohomological dimension theorem,
  right-derived long exact sequence, primitive-root existence, and site axioms.
  `lem-pur-affine-punctured-line-algebra` has no Lean record; its proof is described in the
  theorem docstring but no missing proof-only declaration is assumed to exist.

Edge cases checked: rank zero gives the zero constant module, zero twist and zero cohomology;
q=0 is never subjected to vanishing; q=1 is retained precisely on G_m; q>=2 vanishes on both;
N=1 and all primes including 2 are admitted; characteristic zero is allowed; ℓ equal to a
positive characteristic is excluded exactly by `IsUnit (ℓ : k)`; ζ is a unit since m>0;
finite free S need not be a field or nonzero. The coordinate is t, rather than t^(-1), so the
Kummer sign is fixed. No algebra structure is required on A. All universes and variables are
explicit, with `set_option autoImplicit false` in both files.

Searches: `msearch.py leanfinder` for “etale cohomology of affine line and punctured affine
line with roots of unity coefficients” returned affine-coordinate and etale-locus declarations,
not this computation. `msearch.py loogle '"kummer"'` returned Kummer extensions and
Kummer-Dedekind theory. `msearch.py grep` for
`Kummer|kummer|affineLine.*cohomology|cohomology.*affineLine` in Mathlib AlgebraicGeometry
returned zero hits. `rg` of upstream WeilConjectures and lean/Sheaf found the Kummer sequence,
root constant trivialization, finite torsion twists, and relative affine-line theorems.
The latter assume ring coefficients/abstract Tate data and omit this module coefficient,
generator, and naturality statement, so are not an exact existing declaration. Searching the
item id upstream found no declaration. The current server sources for the newer root pullback
and Tate sheaf were read with `scompile.py --source`; published interfaces were used.
The new-node searches are recorded below and in its `mathlib_searches` verbatim by result.

There is no STATEMENT-DISPUTED flag, no statement correction, and no dependency-record repair.

## New nodes

`def-pur-kummer-module-coefficients` introduces the finite-module coefficient twist and its
insertion morphisms, and makes the unique scalar actions on their existing cohomology explicit.
Its source is the unit's Coefficients paragraph, Stacks 03PK and 03EK. It reuses the existing
root module presheaf, sectionwise tensor and sheafification. Three supporting theorems assert
insertion naturality and annihilation by m for root and twisted cohomology. Their complete
proofs are in docstrings; they are precisely the restriction and scalar-action properties in
this definition node's statement. These theorems supply only proof fields for real
constructions. `kummerRootModulePresheaf` merely transports scalars by the canonical ring lift.

LeanSearch query “tensor roots of unity etale sheaf with a constant finite module” was
unavailable (Internal Server Error). LeanFinder query “tensor roots of unity sheaf with a
constant module and coefficient insertion” returned condensed monoidal structures, general
presheaf tensor products, and representation formulas, not this specialization. Grep of
Mathlib, upstream WeilConjectures, lean/Sheaf, and dag/nodes for the proposed names had no
hits. `blueprint_refs.py search 'module coefficients roots of unity'` returned zero nodes.
The nearby `def-asd-finite-etale-tate-twist` takes commutative ring coefficients and so does
not define the arbitrary-module coefficient functor; its actual roots presheaf is reused.
No existing DAG node carries the module functor together with these insertion maps.

Validation: the prescribed `scompile.py N9 thm-pur-kummer-affine-line` invocation on both
modules completed with exit code 0 and no warnings. Each module was compiled separately in
dependency order, under the wrapper's unchanged 60-second file limit. The delivery dry run is
performed with `deliver2.py N9 thm-pur-kummer-affine-line --no-push`; delivery and the independent
second-reading section belong to the second reader.

## Second reading by N9

I independently read the reviewed node and its six proof steps, both delivered modules,
every statement dependency's record, and the relevant declaration bodies. I read the
blueprint item's original text and unit's Coefficients, Clause (c), and Degrees 0 and 1
paragraphs from the literature mirror. I also read Stacks 03PK (definition of mu and the
Kummer long exact sequence), 03PL (invertibility on the scheme), 03SC (all hypotheses and
the affine bound), 03EK (sectionwise tensor and sheafification), and 01FT (cohomology
computed by injective resolutions). The reviewed stage-1 statement fixes the original
item's ambiguous exponent/characteristic and rank-one wording; this delivery preserves
that reviewed statement. There is no stage-2 statement_change to audit.

My object, hypothesis, and conclusion checklist, with Lean rendering and verdict:

1. Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`. Prime ell,
   invertibility and N at least one: `(ℓ N : ℕ)`, `hℓ : ℓ.Prime`,
   `hℓk : IsUnit (ℓ : k)`, `hN : 1 ≤ N`. The modulus everywhere is `ℓ ^ N`.
   These are precisely the node's assumptions. Invertibility on G_m is supplied by the
   existential `hm`, not imposed as an additional hypothesis. Verdict: exact.
2. R is Z/m and A is any finite free R-module, with no algebra structure on A:
   `ULift.{u+1} (ZMod (ℓ ^ N))`, `A : ModuleCat.{u+1} ...`, `Module.Free ... A`, and
   `Module.Finite ... A`. The ring lift uses `ULift.ringEquiv`. Rank r is represented by
   the arbitrary finite free module itself; neither a basis nor positive rank is required.
   The first coefficient block uses implications for the two predicates, while the
   degree-one block uses instance binders; both quantify over precisely these modules.
   Verdict: exact up to canonical ring transport.
3. The two curves, their structure maps, and inclusion: `curve k false` is literally
   Spec k[t], `curve k true` literally Spec k[t,t^-1], `structureMap` uses the scalar
   inclusions, and `inclusion` uses `Polynomial.toLaurent`. `coordinateUnit` is T 1,
   transported by `ΓSpecIso.inv`; its inverse is T (-1). These fixed schemes have the
   smooth, separated, affine, connected curve properties required in 03SC; Lean does
   not quantify over unspecified schemes with fewer or stronger assumptions. I read
   `IsCurve` and `IsConnectedCurve` in the recorded Curve module. Verdict: exact.
4. Small etale sites, root sheaf, constant coefficients, tensor, and cohomology:
   `smallEtaleTopology` and `rootsOfUnitySheaf` are the existing declarations. The latter
   is exactly `kernel (m • 𝟙 X.gmSheaf)`. I read the root module presheaf's object and
   restriction definitions, not only its name. `kummerRootModulePresheaf` only restricts
   scalars along the ring lift. `kummerModuleTwist` composes the constant presheaf,
   sectionwise `tensorLeft`, and `presheafToSheaf`; `kummerAbelianTwist` forgets scalars.
   Local constant representatives identify this with tensor over the constant ring sheaf,
   as in 03EK and the recorded tensor interface. It is the supported module-valued-sheaf
   encoding of the etale-sheaves node, not a second tensor construction. `Sheaf.H` is the
   source's abelian cohomology model explicitly permitted by the cohomology node's note;
   I also read `Etale.cohomology` and its derived-global-sections definition. Verdict: exact.
5. Primitive root and its degree-zero classes: `ζ : kˣ` and
   `hζ : IsPrimitiveRoot ζ (ℓ ^ N)`. Since m is positive, primitive roots in k are units.
   The two `z b` are required, under `Sheaf.H.equiv₀` and `kernel.ι`, to equal the scalar
   image of ζ in global units. Kernel inclusion is injective, so this specifies the actual
   constant root section uniquely. `kummerCoefficientInsertion` sends x to x tensor a,
   using `TensorProduct.mk ... |>.flip a` and the sheafification unit. Verdict: exact.
6. Degree-zero identifications: the first `∃ e : A ≃ₗ[R] ...` requires, for every a,
   `e a = Sheaf.H.map (kummerCoefficientInsertion ... A a) 0 (z b)`.
   This specifies the map a to ζ tensor a, on each curve, in the required direction.
   Verdict: exact.
7. Vanishing: `∀ q, (if b then 1 else 0) < q → Subsingleton (...)` gives q>0 on
   A1 and q>1 on G_m. Subsingleton is precisely vanishing of these abelian groups.
   `∀ q, Finite (...)` gives finiteness in every degree; the helper supplies the unique
   residue-ring module structures, so these are finite R-modules. Verdict: exact.
8. Kummer generator and degree one: `generator k m hm` is the recorded `kummerδ₀`
   applied to `coordinateUnit k`. The last block's linear equivalence sends every a
   to `H.map i_a 1 (generator ...)`. It consequently gives freeness with the same rank
   as A. For A=R and a=1, the canonical tensor unitor identifies i_1 with the identity
   on mu, so the image is κ_m(t), with the coordinate t rather than its inverse.
   Verdict: exact, including the rank and normalization clauses.
9. Restriction: I read the current published `upperStarRootsOfUnitySheafToRootsOfUnitySheaf`
   body using the prescribed source wrapper and `Etale.cohomologyMap` in its source.
   `rootRestriction` is their composite, in the correct direction. The theorem requires
   it to carry `z false` to `z true`. For coefficients, `∃! res` is characterized on
   all `H⁰(i_a)(x)` by this actual root restriction. The coefficient comparison is
   surjective and pure tensors generate, so these equations uniquely specify the
   canonical coefficient restriction. Tensor pullback naturality gives these equations
   for the usual restriction. The following equation explicitly says res takes
   ζ tensor a to ζ tensor a. This characterization therefore says the same thing as
   restriction being the identity in the displayed A coordinates. Verdict: exact;
   the map is determined, including at rank zero.
10. Coefficient comparison in every degree: `∃ e : (Sheaf.H ... q ⊗[R] A) ≃ₗ[R] ...`
    with its value prescribed on every `x ⊗ₜ a` as `H.map i_a q x` is exactly the
    displayed comparison, not just an abstract isomorphism of its endpoints. Verdict: exact.
11. Naturality: B is another finite free module and f is an arbitrary R-linear map.
    The displayed equality uses `(kummerAbelianTwist ...).map (ModuleCat.ofHom f)`
    and sends `H(i_a)(x)` to `H(i_(f a))(x)`. Pure tensors generate, so this states the
    full comparison square. Taking x=z or x=κ gives naturality of the stated H0/H1
    identifications. Verdict: exact.
12. Scalar extension: S is an arbitrary commutative R-algebra finite free over R.
    The last equivalence in the coefficient block has the node's exact source and target;
    its formula on every x,a,s sends `H(i_a)(x) ⊗ s` to `H(i_(a ⊗ s))(x)`.
    The comparison is determined on generators. In particular it respects the S action
    on the last factor and gives the required degree-zero and Kummer formulas.
    Verdict: exact; no field or nontriviality hypothesis on S is added.

New-node reading (stage 1 and stage 2): `def-pur-kummer-module-coefficients` is absent
from the base DAG and introduces the arbitrary-module specialization required by the
item. Its statement cites precisely its six stmt_deps. The source's finite-free tensor
argument and 03PK/03EK support its definition and insertion maps. I inspected all ten
listed declarations. The functor's map is 1 tensor f by construction, insertion naturality
has the correct U-to-V orientation, the two annihilation theorems say m times each
cohomology element is zero, and the two module instances use `AddCommGroup.zmodModule`
then `Module.compHom`, whose scalar action is uniquely determined. The named proof
of insertion naturality fills a proof field; none of the data is chosen from a mere
existence assertion. The naturality and annihilation statements all appear in the new
node, have source/blueprint/proof docstrings, and retain sorry proofs. The implementation
is total for m=0 as well (mu_0=G_m, ZMod 0=Z); the new node only needs m>=1. Empty X is
allowed by all these helpers, with zero sections and cohomology. The record has exactly
the required kind/status/source/search/created/blueprint/audit/chapter/unit fields; its
blueprint ancestor is this item and the via path is empty. No dependency module or
private copy of an existing dependency was added.

Edge cases: rank zero is admitted by Module.Free/Module.Finite, the empty-basis argument
in proof step 5 covers it, and the unique restriction remains the zero map. q=0 survives
on both curves; q=1 survives only on G_m; all q>=2 vanish. N=0 is excluded precisely by
the node's N>=1, while N=1 and ell=2 are included. Characteristic zero and all positive
characteristics different from ell are covered; ell equal to the characteristic is
excluded precisely by hℓk. The curves themselves are nonempty over a field, so there is
no empty-scheme instance to exclude in the main theorem. The coefficient and scalar
extension universes are u+1, the existing etale cohomology API's universe. Finite modules
and finite free S have representatives there, including the zero module and zero ring;
this imposes no mathematical restriction on the node's finite objects. Increasing u
also accommodates any chosen finite representative. All variables and the universe u
are explicit and `autoImplicit` is false in both modules.

Independent searches (queries differ from the first reader's): LeanFinder
“Cohomology of the multiplicative group scheme generated by the boundary of its
coordinate and finite module tensor coefficients” returned group cohomology H1/H2,
coboundaries, and Hilbert-90 style declarations; no etale curve computation. Loogle
`"rootsOfUnity"` returned rootsOfUnity, rootsOfUnity_eq_ker, rootsOfUnity_zero, and
related subgroup lemmas, not this sheaf statement. LeanFinder “Sheafification of roots
of unity tensor a constant module functor and maps sending a root to a pure tensor”
returned light condensed monoidal sheaf structures, cyclic group resolution tensors,
and the Gabriel-Popescu tensor functor; none is the Kummer module functor. I also made a
fresh LeanSearch request for “Sheaf of modules obtained by tensoring roots of unity with
a constant module”; the service returned Internal Server Error, so this attempt is
recorded as unavailable, not a negative result. The searches are recorded in searches.jsonl. I used rg in Mathlib's
AlgebraicGeometry directory for rootsOfUnity/Kummer and in upstream WeilConjectures and
lean/Sheaf for constant/tensor combinations, affineLine, multiplicativeGroup,
rootsOfUnitySheaf/tensor, ModuleTwist, and CoefficientInsertion, and searched DAG records
for the same notions. I opened upstream Smooth/AffineLine.lean: its four relative
statements use a commutative coefficient ring and abstract HasTateTwist (some also
normalized); they do not specify the arbitrary-module comparison, sections and actual
Kummer generator of this node. The recorded finiteEtaleTateLine likewise takes a ring,
not an arbitrary module. No exact existing declaration or duplicate new notion was found.

Mismatches and changes: no hypothesis, object, or conclusion mismatch was found. I
retained the Lean signatures, all data constructions, and both node statements. I added
the precise DAG dependency ids to proof steps 1–5 of `kummer_affine_line`'s docstring,
so the existing six-step proof is directly usable from its source and named dependencies.
The node's lean.statement remains verbatim equal to the unchanged theorem signature.

Second-reader validation: the prescribed scompile.py invocation on both sibling files
returned exit code 0 and no warnings. It compiled the coefficient module separately,
then compiled both modules in sandbox and library modes in dependency order; every
individual invocation remained below the unchanged 60-second limit. A separate textual
check confirmed both lean.statement fields equal their source signatures verbatim,
all Lean lines are at most 100 characters, and the main node differs from the base
only in lean and the permitted added stmt_dep. The delivery wrapper also recompiles
the final docstring edit and runs the server preflight before pushing.
