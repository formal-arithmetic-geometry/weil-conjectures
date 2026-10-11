## Worker report

TheoremFormalFunctions.lean states `AlgebraicGeometry.theorem_formal_functions` and
`AlgebraicGeometry.globalSections_formal_functions`, both with `sorry`, and nothing is
proved. AffineBaseModuleCohomology.lean supplies two transparent functor composites for
the A-module structures, with fully defined data and no sorry. No statement correction
or disputed statement is needed.

Source checked: Stacks https://stacks.math.columbia.edu/tag/02OC, Theorem 30.20.5 and its
proof. The repository's literature/stacks-project/coherent.tex is absent on this machine,
so the official Stacks page was read. It has exactly the Noetherian-ring, proper-morphism,
coherent-module hypotheses and the canonical isomorphism of limits. Its additional
homeomorphism assertion is intentionally outside this node, as the node source notes.

Hypothesis and clause correspondence:

- A commutative Noetherian ring: `{A : Type v} [CommRing A] [IsNoetherianRing A]`.
- An arbitrary ideal I: `(I : Ideal A)`, with no completeness, locality, proper-ideal,
  or nonzero-ring assumption.
- A scheme and proper structure morphism: `{X : Scheme.{v}}`,
  `(f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]`.
- The extended ideal sheaf I O_X: `(J : X.IdealSheafData)` and `hJ` identify it exactly
  with `(Scheme.IdealSheafData.ofIdealTop
  (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f`.
  `ofIdealTop` first transfers I through A ≅ Γ(Spec A,O); `comap` is the dependency's
  extension of the quasi-coherent ideal along f. J is a named version of the statement's
  introduced ideal, not an extra choice or restriction: its required value exists.
- A coherent O_X-module: `(F : X.Modules)` and
  `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`.
- A fixed p ≥ 0: `(p : ℕ)`. H is `(affineBaseModuleCohomology f p).obj F`.
  Its A-action is restriction along `((Scheme.ΓSpecIso ...).inv ≫ f.appTop).hom`, exactly
  the action by f-sharp described in proof step 1. No independent module structure is
  assumed.
- I^n F and the quotient: `formalModuleQuotient J (n+1) F` is the dependency's actual
  cokernel of the inclusion of the ideal-module product, using its shared ideal powers.
- H^completion: `AdicCompletion I ((affineBaseModuleCohomology f p).obj F)` is exactly
  the compatible sequences in H/(I^n • top), using Mathlib's module completion.
- Quotient-induced maps and their annihilation of I^n H: the existential A-linear
  family `θ n` has the first factorization equation
  `(θ n).comp (Submodule.mkQ ...) = (C.map (formalModuleQuotientπ ...)).hom`.
  This specifies the unique factorization of the actual cohomology map. Since mkQ kills
  I^(n+1)H, the equation also asserts precisely the claimed vanishing; no arbitrary
  comparison maps are allowed.
- Compatibility with both systems: the second conjunct, for every n ≤ m, equates
  the cohomology of `formalModuleQuotientMap J (𝟙 F) ...` composed with θ m to θ n
  composed with `AdicCompletion.transitionMap ...`.
- The inverse limit on the right: `limit (formalCompletionSystem J F ⋙ C)` in ModuleCat A.
  The formal-completion functor uses op n for level n+1 and the canonical reductions.
- The canonical map is an A-module isomorphism: the last conjunct supplies an actual
  `ModuleCat.of A (AdicCompletion ...) ≅ limit (...)`; its hom composed with every
  `limit.π ... (op n)` equals `ModuleCat.ofHom ((θ n).comp (AdicCompletion.eval ... (n+1)))`.
  This is exactly lim θ, fixing its components even on completed elements, rather than
  merely asserting two objects are isomorphic.
- The p=0 global-section assertion: `globalSections_formal_functions` repeats those
  same factorization, compatibility, and projection equations with
  `affineBaseGlobalSections f` = the recorded global-sections functor followed by the
  same restriction of scalars. It states the assertion for actual Γ(X,F) and Γ(X,F/I^nF).
  Thus the final clause is explicit, not left only to an unstated H^0 ≅ Γ bridge.

Dependency declarations read and used:

- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`, every ideal finitely generated.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `AlgebraicGeometry.IsProper`.
- Mathlib.AlgebraicGeometry.IdealSheaf.Functorial:
  `AlgebraicGeometry.Scheme.IdealSheafData.comap` (def-nagata-extended-ideal).
  Mathlib.AlgebraicGeometry.IdealSheaf.Basic: `Scheme.IdealSheafData.ofIdealTop`.
- Sheaf.AlgebraicGeometry.Coherent: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- Sheaf.AlgebraicGeometry.CoherentFormalModule: `formalModuleQuotient`,
  `formalModuleQuotientπ`, `formalModuleQuotientMap`, `formalCompletionSystem`.
  Its full source was read; the quotient is a cokernel and the system is not constant.
- Sheaf.Paper.PQFCohomology: `sheafCohomologyAndHigherDirectImages` identifies the
  recorded functor `RingedSpace.moduleCohomology` as the cohomology meant here.
  The full signature/docstring were read. No extra higher-direct-image hypotheses are
  needed for ordinary cohomology.
- Sheaf.Topology.RingedSpaceModuleCohomology: `RingedSpace.moduleCohomology` and
  `RingedSpace.globalSectionsFunctor`, used through the new transparent composites.
- Mathlib.RingTheory.AdicCompletion.Basic: `AdicCompletion`, `eval`, `transitionMap`.
- Mathlib.Algebra.Category.ModuleCat.ChangeOfRings: `ModuleCat.restrictScalars`.
- Mathlib.AlgebraicGeometry.GammaSpecAdjunction: `Scheme.ΓSpecIso`.

Edge cases checked before drafting: I=0 gives the constant positive-level quotient F;
I=A gives zero quotients and zero completion. F=0 and the empty scheme give zero modules.
The zero ring is permitted (Spec is empty). There is no positive-characteristic restriction.
p=0 is covered both by the general theorem and the actual-global-sections statement.
The sheaf system omits level zero, as its dependency does; Mathlib's completion retains
level zero H/H=0. This adds a unique zero coordinate and changes no inverse limit.
Every universe and variable is explicitly bound, with A and X in the same arbitrary
universe. Countable inverse limits of ModuleCat exist; no extra HasLimit hypothesis is
assumed. J is a quasi-coherent ideal supplied by extension from the affine base; properness
over a Noetherian ring implies X is Noetherian, but no extra hypothesis is imposed.

Searches made (also logged in searches.jsonl): LeanFinder query "completion of coherent
sheaf cohomology on proper scheme theorem on formal functions" returned scheme-limit
results, not formal functions. Loogle "AdicCompletion, LinearMap" returned completion
maps, not geometry. Mathlib grep "formal.function|FormalFunction|formalFunctions"
returned only unrelated conformal-function and monoid-algebra text. The source and
Sheaf trees were searched for formal-functions and adic/cohomology combinations; there
is no existing statement. `grep -rn` for this item in WeilConjectures gave no result;
upstream name records contain no entry or declaration-name collision.
The new node's searches are described below. Server combined compile passed cleanly
in 2.4 seconds (no errors or warnings). Both theorem docstrings carry all seven proof
steps of the node, with the ML/Artin-Rees input explicitly named.

## New nodes

`def-weil-pbc-affine-base-module-cohomology` defines A-valued global sections and
cohomology over f:X→Spec A by composing the recorded Γ(X,O_X)-valued functors with
Mathlib restriction of scalars along the structure ring map. Source: Stacks 02OC's
A-module H^p(X,F), and 01DZ for Γ and its right derived functors. The module defines
`affineBaseModuleCohomology` and `affineBaseGlobalSections`, and contains no theorem
or sorry. No independent cohomology definition is introduced. This missing interface
is directly cited in the item's stmt_deps.

LeanSearch query "cohomology of O_X modules as A modules for a scheme over Spec A
restriction of scalars global sections" failed with the service's Internal Server Error
(recorded as unavailable). LeanFinder query "cohomology module functor on a scheme
over an affine base restriction of scalars" returned pullback, tilde, pushforward, and
sheaf restriction of scalars, none defining the desired A-valued functor. Mathlib grep
"affineBase.*(Cohomology|Sections)|moduleCohomology|cohomologyOver" in AlgebraicGeometry
returned no hit. Source grep for the same names returned no hit. Sheaf grep found no
existing affineBase or cohomologyOver declaration. Broad DAG grep found related
base-change/tensor/derived-coefficient nodes, not this interface; notably
`def-pc-module-cohomology-base-change` concerns tensoring complexes of ring modules.
`tools/blueprint_refs.py search 'affine base module cohomology'` found zero nodes.
`FieldLinearModuleCohomologyOperations.scalarMap` only treats a field and sections;
it is neither arbitrary-ring cohomology nor the stated functor. The new definition
reuses the recorded ringed-space functors, not any private replacement.

## Second reading by V1

I independently read the item's node and both delivered modules, then the recorded
statement-dependency nodes and the definitions used by their declarations. I found no
mathematical mismatch and kept the Lean and node records unchanged. This second reading
adds the independent review and its validation to this report.

Source: the local Stacks directory is absent. I read the official pages
https://stacks.math.columbia.edu/tag/02OC and https://stacks.math.columbia.edu/tag/01DZ,
and fetched the official stacks/stacks-project coherent.tex and cohomology.tex into
this item's scratchpad. In coherent.tex I read the section's standing notation at
lines 5324ff, Lemma 02OB at 5553ff, and Theorem 02OC and its proof at 5648ff.
The standing notation defines ideal products by the image of multiplication; there
is no additional completeness, locality or flatness hypothesis. The theorem's
homeomorphism clause is expressly excluded by this node's source record.

Object, hypothesis and conclusion checklist (all verdicts: exact):

1. A is a commutative Noetherian ring: `{A : Type v} [CommRing A]
   [IsNoetherianRing A]`. The recorded Noetherian declaration means every ideal is
   finitely generated. There is no field, domain, nonzero or completeness instance.
2. I is any ideal of A: `(I : Ideal A)`. No restriction to a maximal or proper ideal.
3. X is a scheme and f is proper over Spec A: `{X : Scheme.{v}}`,
   `(f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]`. I read the Mathlib class:
   separated, universally closed, locally of finite type; universal closedness supplies
   quasi-compactness, giving finite type as required.
4. The ideal sheaf is precisely I O_X: `J : X.IdealSheafData` with `hJ` equating J
   to `ofIdealTop (I.map (ΓSpecIso ...).inv.hom) |>.comap f`. The inverse of ΓSpecIso
   has source A and target Γ(Spec A,O). `ofIdealTop` extends that ideal on affine opens;
   `comap` is the recorded extended ideal (kernel of the base-changed closed immersion).
   J and hJ name a uniquely specified object and impose no extra condition on f or I.
5. F is a coherent O_X-module: `(F : X.Modules)` and
   `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`. I read Coherent.lean: finite
   type and finite-type kernels for every finite-free map on every open, as in the node.
6. p is any nonnegative integer: `(p : ℕ)`. H is
   `(affineBaseModuleCohomology f p).obj F`. The composite uses the recorded
   `RingedSpace.moduleCohomology`, defined as the right derived functor of evaluation
   at the whole space. It restricts scalars along `(ΓSpecIso ...).inv ≫ f.appTop`.
   Thus the A-action is the structure-map action, with no freely chosen module instance.
7. The sheaf quotient F/J^n F is `formalModuleQuotient J (n+1) F`.
   I read CoherentFormalModule.lean and IdealModuleProductStalk.lean: the product is
   the image of multiplication, powers are recursively actual products, the quotient
   is its cokernel, and `formalModuleQuotientπ` is the cokernel projection.
8. The completion is `AdicCompletion I H`. I read Basic.lean: compatible elements
   of every H/(I^n • top), with `transitionMap` the canonical quotient reductions.
9. The quotient-induced maps are exactly `C.map (formalModuleQuotientπ ...)`, for
   C = `affineBaseModuleCohomology f p`. Each θ is an A-linear map out of the actual
   quotient H/(I^(n+1)H). The first conjunct `(θ n).comp (Submodule.mkQ ...) =
   (C.map ...).hom` asserts its factorization and therefore annihilation of I^(n+1)H.
   Surjectivity of mkQ fixes θ uniquely; this is not an arbitrary family of maps.
10. Compatibility is the second conjunct for every n ≤ m, using the cohomology of
    `formalModuleQuotientMap J (𝟙 F) (Nat.succ_le_succ h)` and
    `AdicCompletion.transitionMap ... (Nat.succ_le_succ h)`. I read the former's
    cokernel-desc definition and `formalCompletionSystem`: these are exactly the
    reductions of the same quotient projections, oriented from larger to smaller powers.
11. The right limit is `limit (formalCompletionSystem J F ⋙ C)` in ModuleCat A.
    The existential isomorphism e has source the completed H. Its composite with every
    `limit.π ... (op n)` is `ModuleCat.ofHom ((θ n).comp (AdicCompletion.eval ...
    (n+1)))`. These equations on all completed elements specify lim θ, hence the
    canonical comparison is an isomorphism, not merely an abstract equivalence.
12. The final global-sections clause is `globalSections_formal_functions`, with
    exactly the same factorization, compatibility and component equations for
    `affineBaseGlobalSections f`. This functor evaluates F at the whole space, then
    restricts scalars by the same map. It states the actual Γ assertion independently
    of a later H^0 comparison proof. Quantifiers introduce A,I,X,f,J,F before p and
    the induced family, exactly as required; the degree-zero clause needs no p binder.

Edge cases: p=0 is included explicitly and in the general theorem. The positive index
n+1 includes all n≥1; the omitted n=0 quotient is zero because I^0 H=H and J^0 F=F,
so adding its unique zero coordinate changes neither inverse limit nor comparison.
I=0 gives the constant positive quotient system; I=top gives zero quotients and zero
completion. F=0, X empty and the zero base ring are all permitted. Characteristic is
unrestricted. Both universes are explicitly declared and all variables bound; a common
arbitrary universe for the ring, scheme and module sections is the project's scheme
encoding and can be enlarged to contain any given data. The countable diagram has the
usual ModuleCat limit with no extra finiteness or HasLimit assumption.

H4 independent searches: msearch LeanFinder query "adic completion comparison
isomorphism for proper coherent cohomology" found module completion congruences and
local cohomology, no formal-functions theorem. Loogle `AdicCompletion, ModuleCat`
returned no hits. LeanFinder "scheme cohomology valued in modules over the base ring"
found Scheme.Modules and sectionwise module structures, no base-valued cohomology
functor. Independent rg searches for formal-functions names, affineBase names and
cohomology/restrictScalars combinations in Mathlib, WeilConjectures, Sheaf and upstream
name records found only unrelated text and uses of the theorem, no existing declaration.
Broader base-cohomology searches found DirectImage/Sections.lean; I opened it: its
semilinear comparison uses the abelian-sheaf H and higher direct images with additional
quasi-coherence hypotheses, not this definition or theorem. DAG searches likewise found
base-change and affine-section comparisons, not the missing scalar-restriction interface.
The worker's LeanSearch service failure is documented; its successful LeanFinder and
grep searches and my independent searches do not reveal a duplicate.

New-node review: def-weil-pbc-affine-base-module-cohomology correctly packages only the
two composites with restriction of scalars. Stacks 01DZ gives module cohomology valued
in modules over Γ(X,O), and 02OC uses its A-action through f. Both definition bodies
are fully specified functor composites, without sorry or a private replacement for
cohomology. I checked the new node's cited dependencies, chapter/unit, creation,
blueprint ancestry/via, search records, empty proof fields, audit and lean fields
against §5. No dependency modules are added and no statement correction is present.

H5–H9: exactly two theorem proofs are sorry; both docstrings give all seven node proof
steps including the bound from lem-weil-pbc-ml-cohomology-powers-ideal. Every declaration
and module has its source and owning blueprint id. No local notation, private definition,
hollow data, hidden let/show binder, unbound universe or overlong line appears. Both
recorded lean.statement strings occur verbatim as the signatures in their files.

Validation: scompile compiled both modules together in dependency order in 2.6 seconds,
exit code 0, with no warnings or errors. The initial invocation used relative paths
from the repository instead of the sandbox; rerunning with absolute sandbox paths
resolved that invocation error without changing code.
