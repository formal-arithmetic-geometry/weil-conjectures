## Worker report

The module `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` states the item in
`AlgebraicGeometry.ProEtale.SemilinearProperOpen`. The primary declaration is
`semilinearProperOpenMatePasting`; the other assertions of the node are the
recorded declarations `gamma_adjunct`, `gamma_identities`,
`compositor_associativity`, `gamma_scalarRestriction`, `gamma_evaluation`,
`gamma_finite`, and `pi_components`. All theorem proofs are `sorry`. Definitions
have actual data: compositions of existing functors, adjunction mates,
localizations, or choices from uniquely determining universal properties.
There is no choice of a free comparison or of an arbitrary isomorphism.

Hypotheses and clauses, in the order of the node:

1. The arbitrary inverse ring sequence is `(C : ℕ → CommRingCat.{u+1})`
   and `(τ : ∀ n, C (n+1) ⟶ C n)`. Lean index zero denotes the first level.
   `coefficients` and `transition` use Mathlib's actual constant-sheaf functor.
   No flatness, surjectivity, finiteness, nonzero-ring or boundedness hypothesis
   is imposed on this sequence.
2. `ringSystem`, `Modules`, and `Derived` are abbreviations for the recorded
   `SemilinearSections.systemRing`, `Systems`, and `DS`, respectively. Their
   universes are explicitly `(u+1,u,u+1)`. These are modules on the vertical
   sequence site, hence strict semilinear systems with the prescribed
   transitions, and their ordinary unbounded derived category. They are not
   diagrams of separately localized categories. The original Mathlib site
   `Scheme.ProEt` has object universe u+1 and morphism universe u; the standard
   essentially-small presentation implements the node's small-site convention.
3. `siteMap` is index-preserving geometric base change. `coefficientMap` is
   uniquely characterized on each component by the existing constant-section
   structural ring map. `push` is the existing sheaf-of-modules direct image
   for that ringed sequence site. `pull` is its left adjoint, determined up to
   the unique adjunction-preserving isomorphism. `pull_exact` asserts exactness
   componentwise. `P` is its exact derived localization; `R` is total derived
   `push` (the node writes S). `adj` supplies precisely P ⊣ R, with its actual
   unit and counit. K-injectives are on the system site; evaluation need not
   preserve them.
4. For `[IsOpenImmersion j]`, `extension` is the left adjoint of `pull j`;
   `ordinaryOpenAdj`, `extension_exact`, `J` and `jAdj` retain its ordinary and
   exact derived adjunctions. The section identification of the universal
   extension makes the open unit identity over the open. `jAdj_unit_isIso`
   records that identification. `betaInvApp` is exactly the transpose of the
   pulled-back open unit; `beta` is its inverse in a cartesian open square.
   Thus the open normalization is fixed, rather than an arbitrary open
   comparison. This is the same transpose specified in the dependency.
5. The direct-image compositor `sComp` is literally right-adjoint conjugation
   of `pComp`. `pushComp` itself is uniquely specified by restriction along
   Mathlib's canonical iterated-pullback comparison; `pullComp` is its left
   adjoint conjugate and `pComp` its exact localization. `pushId`, `pId`,
   `sId`, `jComp` and `jId` keep the corresponding identity conventions.
6. The square binds all four schemes and arrows, `[IsOpenImmersion k]`,
   `[IsOpenImmersion i]`, `[QuasiCompact k]`, `[QuasiCompact i]`, `[IsProper r]`,
   `[IsProper p]`, and `h : k ≫ p = r ≫ i`. There is no cartesianness
   assumption on this square. `pullback p i`, `pullback.fst`, and
   `pullback.snd` are the specified fibre product and projections. The lift
   is the dependency's `StrictTower.squareLift k r p i h`, with its existing
   open and closed immersion instances. It is not a newly chosen factorization.
7. `openToS` is the canonical open-to-direct comparison, defined by the
   adjunction unit and inverse open unit. `openToS_isIso` identifies J_s and
   R_s for clopen s. `pi` is η_s followed by that identification.
   `pi_components` explicitly states identity on the image under the open
   unit and zero on the complementary open. No arbitrary splitting is supplied.
8. `alpha` is exactly beta, followed by J_b pi_s P_q, followed by the J and P
   compositors and the two fibre-product lift identities. `gamma` is exactly
   `mateEquiv (adj r) (adj p) alpha`; expanding Mathlib's mate formula gives
   the displayed η_p / alpha / ε_r word in the node.
9. `cartesianConjugate` is explicitly `conjugateIsoEquiv` of beta inverse for
   the composite adjunctions; this is the FIRST lambda identification.
   `restrictFactor` gives P_b J_k ≅ J_s using the open unit. `lambda` composes
   those maps, clopen `openToS`, and `sComp s q`, transported along q s = r.
   `gamma_adjunct` states BOTH the J_i ⊣ P_i adjunct equation with lambda
   inverse and the restriction equation lambda ∘ P_i gamma = identity, with
   the open unit inserted explicitly.
10. The three conjuncts of `semilinearProperOpenMatePasting` are the vertical,
    horizontal and base-change equations. In the first two, explicit `sComp`
    and `jComp` arrows express the node's canonical identifications. In the
    third, `exchange` is the canonical pullback-square mate of `squareP`;
    the two beta factors and the two exchange factors occur in exactly the
    node's order. The generic cartesian cube can be instantiated by the
    chosen fibre products of any base change. All equations live in the
    derived semilinear-system category, before evaluation.
11. `compositor_associativity` states the coherence of P, R and J compositors.
    Iterating the binary pasting equations identifies every parenthesization
    with the outer-square gamma. `gamma_identities` states the identity cases
    with `sId` and `jId`. Every square declaration permits r = identity with
    noncartesian clopen lift; no refinement case has been removed.
12. `B`, its commutative ring structure, maps `φ : ∀ n, B →+* C n`, and
    compatibility `hφ` are bound in ScalarRestriction. `rhoOrdinary` is uniquely
    determined by its evaluated scalar-restriction functors and actual
    transition section maps. It is exact. `rhoP` comes from the ordinary
    direct-image identity on sections via the adjunction transpose. `rhoR`
    is DEFINED as the derived mate of `rhoP.inv`, and asserted invertible.
    `rhoJ` is also defined via the open-adjunction transpose. The equation
    `gamma_scalarRestriction` compares gamma with the recorded
    `StrictTower.gamma B` using precisely these specified arrows, at the
    system level. This does not infer equality by scalar-restriction faithfulness.
13. `levelTower n` is the actual dependency evaluation at n followed by the
    constant strict diagram over C_n. `E` is its exact derived localization.
    The constant diagram retains the original n-th level at every index;
    evaluating it at index zero recovers that level. `evalP`, `evalR` and
    `evalJ` use the same explicitly normalized mate constructions as above.
    `gamma_evaluation` states equality with `StrictTower.gamma (C n)` under
    these canonical comparisons, rather than only an isomorphism conclusion.
14. In `gamma_finite`, the ONLY extra mathematical assumptions are finite C_n
    and its retained bounded-below etale origin. The origin is passed as the
    existing bundled `StrictTower.ScalarEtaleOrigin` at the actual n-th input.
    `hC` fixes that bundle's coefficient carrier to C_n, and `hscalar` fixes
    its scalar map to the identity. These are coordinate constraints on the
    existing general witness type, not new hypotheses on the scheme, ring,
    input, or etale antecedent. A C_n origin gives such a bundle by setting
    its carrier to C_n, scalar map to identity, and retaining its D+ object,
    `Scheme.EtaleOriginWitness`, and specified input isomorphism. Conversely,
    transport along hC and hscalar recovers exactly that C_n origin. The
    bundle carries its finite discrete topology; no topology hypothesis is
    imposed on C_n. The displayed comparison uses the dependency's actual
    `finiteSource`, `finiteTarget`, and particular `finiteGamma`, together
    with `evalSource` and `evalTarget`. It retains w.origin and w.iso, hence
    identifies the specified finite comparison, rather than merely some
    isomorphism of its source and target. The broader coefficient fields of
    the reused bundle are fixed by hC and hscalar; no arbitrary coefficient
    map or scalar extension is allowed in this clause.
15. No declaration assumes faithfulness of evaluation or scalar restriction
    on derived morphisms. Only detection of isomorphisms is used in the
    proof plans for the invertibility assertions.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Sites.ProEtale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections` and its actual
  models `systemRing`, `Systems`, `DS`, `evaluation`, `res`, plus the derived
  evaluation/mate normalization. The general existence theorem is not used
  to choose unknown data; the actual models are used directly.
- `Sheaf.SixFunctors.OpenTensorNormalization`:
  `SheafOfModules.openTensorNormalization` and its specified open-unit
  transpose; `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`
  is used directly by `jAdj`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `conjugateIsoEquiv`,
  `mateEquiv_hcomp`, `mateEquiv_vcomp`, `unit_conjugateEquiv_symm`.
- Mathlib's `IsOpenImmersion`, `QuasiCompact`, `IsProper`, `IsClosedImmersion`,
  and categorical `pullback`, projections and lift; the scheme-properties
  dependency is a convention node with no additional declaration.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`:
  `AlgebraicGeometry.ProEtale.StrictTower.normalizedProperOpenCalculus`,
  `gamma`, `squareLift`, its clopen instances, canonical G/R/J and adjunctions,
  `finiteGamma`, `finiteSource`, `finiteTarget`, and `gamma_evaluation`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `Scheme.proEtaleRingSheafChangeAdjunction`, its canonical inverse-image
  comparison and direct-image adjunct normalization. These fix the proof
  plan of `rhoPullInv_isIso` and `rhoR_isIso`; the comparisons themselves are
  constructed as mates of section-normalized ordinary comparisons.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `Scheme.FixedEtaleOriginWitness`, and its publicly reexported finite
  ringed-coordinate `Scheme.EtaleOriginWitness`, used by the retained origin in `gamma_finite`.

The proof-only prerequisite `lem-sp-varying-ring-proper-open-pasting` has no
published declaration. No missing module is imported: this delivery supplies the
intrinsic constructions directly on the already recorded semilinear models.
The other proof-only prerequisite, the conjugate-unit equation, is available
from Mathlib's Mates import. No dependency record needs repair.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "Intrinsic proper open mate and pasting for derived
  strict semilinear module systems"`: eight unrelated tensor/module results;
  no exact match.
- `msearch.py ... loogle '"mateEquiv", "conjugateIsoEquiv"'`: no result.
- `msearch.py ... leansearch "Proper open base change pasting for inverse
  systems of sheaves of modules"`: eight general sheaf/module results;
  no exact match.
- `msearch.py ... grep 'proper.*open.*mate|semilinear.*pasting' CategoryTheory`:
  no result in Mathlib.
- `rg` and the item-id grep in the upstream `WeilConjectures` tree, and `rg`
  in the project's `lean/Sheaf`: no existing varying-coefficient intrinsic
  proper/open mate theorem; the constant-tower and general semilinear models
  were found and reused. The upstream-name index likewise has no declaration
  of this namespace or the item.

Edge cases checked against the source before and during the second reading:
empty scheme and empty open (extension and the selected clopen component are
zero); full/identity open (unitors give the identity equations); identity
vertical maps; r = identity in a noncartesian refinement; zero coefficient rings;
nonflat transitions; constant or changing ring sequence; index zero (first
level); unbounded input without finite origins; separately bounded-below origin
at a finite level (no common lower bound requested). None is excluded by a
hidden Nonempty, nonzero, flatness, cartesianness or boundedness assumption.
The two site universes remain unequal. No statement correction or mathematical
fault was needed.

## Second reading by Q66

The dispatcher explicitly prohibited starting another agent; this is a separate
second pass by the same worker, not a claimed independent-agent review. I reopened
the node, its source passages (Stacks 0F7B/C/D/F and the blueprint coherence
step), and the module, and compared every clause using the mapping above.

The finite-origin probe showed that elaborating a fresh localized restriction
functor introduced unconstrained universe metavariables in its abelian instance.
The final clause instead takes the dependency's ALREADY BUNDLED witness and
fixes its carrier and scalar-map fields to C_n and identity. This preserves
exactly the input witness, its D+ antecedent and its specified comparison, while
avoiding a second elaboration of the dependency's localizations.

The second pass found and repaired: (1) direct-image scalar comparison needed
its INVERSE before the inverse-image mate transpose; (2) unqualified evaluation
resolved to a different Scheme declaration, so the model's full namespace was
written; (3) the derived-system and ring-sheafification instances needed explicit
universe normalization; (4) the original draft had not yet expressed evaluation
and the particular finite comparison, now `gamma_evaluation` and `gamma_finite`;
(5) the identity/zero projector clause and compositor parenthesization coherence
now have explicit assertions rather than only docstrings. I checked the order
of every alpha, lambda, scalar, finite and base-change composite against its
source and target. No clause is replaced by arbitrary maps, bare existence of
an isomorphism, or a faithfulness hypothesis.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.
