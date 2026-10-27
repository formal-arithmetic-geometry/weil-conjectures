## Worker report

The module `Sheaf.AlgebraicGeometry.CartesianModuleFppfRealization` states
`CategoryTheory.cartesian_module_fppf_realization`. Its sole proof is `sorry`.
There are no new definitions, helper axioms, dependency repairs, new nodes, or statement
corrections. The existing statement and proof plan are preserved.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The size convention is explicit `universe u v w`: schemes have universe `u`, and the
  total category retains its independent morphism and object universes through
  `BasedCategory.{v, w}`. The sheaf uses the dependency's ambient coefficient universe
  `max (u + 1) v w`; there is no equality between these universe parameters.
* The scheme S is `{S : Scheme.{u}}`. The total category with projection to Sch/S is
  `C : BasedCategory.{v, w} (Over S)` and the exact lift/strong-cartesian condition is
  `hC : IsFibredInGroupoids C`. All objects and arrows, including fibre automorphisms,
  are retained.
* The big fppf topology and ring sheaf are the existing `moduliFppfTopology C` and
  `moduliModuleRings C hC`. Their covers are the inverse images of fppf scheme covers,
  and the ring values are the canonically ULifted global regular functions.
* The family M_x is `M : ∀ x : C.obj, ((moduliSchemeForget C).obj x).Modules`.
  `hM` requires precisely `SheafOfModules.IsQuasicoherent (M x)` for every x;
  finite type, coherence, Noetherianity and flatness are not required.
* The prescribed theta for every arrow a:y to x is an isomorphism from
  `(Scheme.Modules.tensorPullback ((moduliSchemeForget C).map a)).obj (M x)` to `M y`.
  This is the dependency's actual tensor pullback, not an unrelated pullback functor.
* `theta_id` identifies its hom with `tensorPullbackSectionId` after transporting
  the functor's image of the identity to the identity scheme map.
* `theta_comp` uses `tensorPullbackSectionComp` from the composite pullback to the
  iterated pullback, followed by pullback of theta_a, followed by theta_b. The
  `map_comp` equality accounts for the projection functor's composite. This is exactly
  theta_(a b) = theta_b composed with b^*(theta_a), with Lean composition b ≫ a.
* The conclusion gives `G : SheafOfModules (moduliModuleRings C hC)` and additive
  equivalences `e x : G.val.obj (op x) ≃+ Γ(M x, ⊤)`. The structural scalar equation
  identifies the action with the usual section action; `r.down` removes only the
  dependency's canonical ULift, and `eqToHom (Scheme.Γ_obj_op ...)` identifies the
  global-sections functor with the section ring used by Scheme.Modules.
* The restriction equation specifies EVERY arrow and EVERY section: use the unit of
  `tensorPullbackSectionAdjunction`, restrict from the inverse image of top to top
  using `preimage_top.ge`, then apply `(theta a).hom.app ⊤`. This is exactly pullback
  of a section as 1 tensor s followed by theta. The additive equivalences and this
  equation identify G with the entire prescribed presheaf, including its restrictions
  and operations, not just with unrelated objectwise section sets. Expressing this by
  section coordinates avoids a false definitional equality across universes.
* Membership in `SheafOfModules` supplies the fppf sheaf condition on the same presheaf;
  `SheafOfModules.IsQuasicoherent G` supplies local presentations by arbitrary small
  free modules. No algebraicity, finiteness, representability or flatness hypothesis
  appears. Existence with these fully specified coordinates is the stated realization.

Dependency declarations inspected and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `.Hom`, `.Γ_obj_op`.
* `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids` (publicly exposed by the site
  dependency): `CategoryTheory.IsFibredInGroupoids`, which is the projection's
  `IsFibered` condition together with strong cartesianness of every arrow.
* `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`: `moduliSchemeForget`,
  `moduliFppfTopology`, `moduliModuleRings`, and its slice sheafification instances.
* `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes Mathlib's
  `SheafOfModules.IsQuasicoherent`; the stronger finite-type conjunction is not used.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback`,
  `tensorPullbackSectionAdjunction`, `tensorPullbackSectionId`,
  `tensorPullbackSectionComp`. Read the normalized adjunction and actual section unit.
* Proof-only import `Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence`:
  `scheme_big_fppf_quasicoherent_equivalence`; its signature identifies all section,
  scalar and restriction coordinates of the scheme-associated fppf sheaf.
* `def-trf-space-quasi-coherent-module` explicitly retains the general Mathlib match
  `SheafOfModules.IsQuasicoherent`. Its already transitively imported module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule` supplies that predicate,
  so no algebraic-space hypothesis or duplicate quasi-coherence definition is used.
* `def-weil-size-convention` is a metatheoretic convention, with no module to import.

Source checked: `literature/stacks-project/stacks-sheaves.tex`,
lemma-characterize-quasi-coherent (06WI) and lemma-quasi-coherent (06WK), including the
converse proof's use of the scheme-associated sheaf. The declaration docstring contains
all five DAG proof steps: functorial section restrictions; ringed slice equivalence;
scheme-associated realization and naturality on arbitrary pullback sections; sheaf
gluing; and transfer of local free presentations.

Edge cases checked mathematically before writing and rechecked against the signature:
empty total category (all family conditions vacuous, empty-site module sheaf allowed),
empty scheme (its unique zero module and empty fppf covers allowed), zero modules,
non-affine and non-separated schemes, non-flat arbitrary arrows, arbitrary-rank local
presentations and arbitrary characteristics. Nontrivial fibre automorphisms are not
quotiented out, and theta can carry their full action subject only to the stated
identity and cocycle. Identity and composition normalizations use the section-normalized
canonical comparisons. No nonempty or finiteness binder is hidden in the signature.

Searches made using the prescribed msearch wrapper:

* LeanFinder: "Compatible quasi coherent modules on a category fibred in groupoids
  define a quasi coherent fppf sheaf by sections". Eight hits, all generic
  `SheafOfModules.QuasicoherentData`/`IsQuasicoherent` definitions or fields; no realization.
* Loogle: `SheafOfModules.IsQuasicoherent, PresheafOfModules`. Zero hits.
* Mathlib grep: `cartesian|fibred|fibered|fppf`, subdirectory
  `Algebra/Category/ModuleCat/Sheaf`. Zero hits.
* LeanSearch: "Compatible quasi coherent modules on a fibred groupoid form a sheaf
  on the fppf site". Eight hits on general quasi-coherence definitions and constructors,
  none on this compatible-family realization.
* Local `rg` over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  `cartesian.module|cartesianModule|moduli.*Module|Moduli.*Module|fppf.realization|fppf_realization`
  and `cartesian_module_fppf_realization|CartesianModuleFppfRealization|compatible.*quasi.coherent`.
  Found the forward restriction interface `ModuliSchemeRestriction` and the coherator,
  neither of which realizes an arbitrary supplied compatible family. Read its signature
  to check this distinction. No existing declaration of the requested converse.
* `grep -rn lem-sfb-cartesian-module-fppf-realization lean/WeilConjectures`: no hits.

No statement dispute or source fault found. Compilation uses only scompile.py; the
first pass exposed a scalar-ring instance mismatch and a projection-parenthesization
error, repaired by the canonical ring equality and explicit parentheses. The next pass
elaborated the statement and reported only a long line, which has been wrapped.

## Second reading by NU

Author's second pass, not an independent review; the maintainer's independent review
follows delivery as required by the dispatcher brief. Reopened the DAG statement and
Lean signature and checked each binder and conjunction listed above. In particular the
composition comparison has direction composite-to-iterated; theta_b follows b^*theta_a;
the scalar transport is the canonical ring equality; all restriction maps are fixed by
the unit rather than supplied arbitrarily; and quasi-coherence is the local-presentation
predicate. This pass found no missing hypothesis or clause and introduced no mathematical
change. Every variable and universe is explicit, no helper definition or local notation
is needed, and the only postponed theorem is the node itself.
