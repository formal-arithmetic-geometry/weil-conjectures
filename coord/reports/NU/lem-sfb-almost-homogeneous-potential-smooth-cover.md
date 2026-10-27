## Worker report

The module `Sheaf.AlgebraicGeometry.AlmostHomogeneousPotentialSmoothCover` states
`AlgebraicGeometry.exists_almostHomogeneous_potential_smooth_cover`, with a single `sorry`.
It defines no new notions, changes no mathematical statement, and repairs no dependency.
The source is Anantharaman, Proposition 4.2.3 (OCR 4,2,5), printed pp.58–59,
and Appendix II Corollaries 2–3, p.73. I read these in the primary Numdam PDF:
https://www.numdam.org/article/MSMF_1973__33__5_0.pdf (PDF pages 54–55 and 69).
The current blueprint is the latest snapshot recorded as main-20261024 in COMMITS.txt.
The item has inherited null blueprint ancestry, preserved unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base is `R : Type u` with `CommRing`, `IsDomain`, `IsNoetherianRing`,
  `IsIntegrallyClosed`, `hdim : ringKrullDim R = 1`, and
  `hmax : Set.Finite {m : Ideal R | m.IsMaximal}`. Its fraction field is the canonical
  `FractionRing R`; its affine scheme is `Spec (.of R)`.
- `G X : Over (Spec (.of R))` supplies the actual structure morphisms.
  `GrpObj G` includes multiplication, unit, inverse, and all group laws. `ModObj G X`
  supplies the action and its laws; no commutativity is imposed.
- `IsSeparated G.hom`, `Flat G.hom`, `LocallyOfFiniteType G.hom`,
  `QuasiCompact G.hom` give precisely the separated flat finite-type group.
  `IsSeparated` is Mathlib's closed-diagonal predicate.
- `IsSeparated X.hom`, `Flat X.hom`, `LocallyOfFinitePresentation X.hom`,
  `QuasiCompact X.hom` give the separated flat finitely presented space. The remaining
  quasi-separatedness in finite presentation follows from the stated separatedness.
- `n : ℕ`, `V : Fin n → Over (Spec (.of R))`, and open immersions `inc j : V j ⟶ X`
  specify the finite open family. `ModObj G (V j)` and `IsModHom G (inc j)` express
  invariance including all nonreduced test schemes. `hcover` states that these opens cover.
  Giving the restricted action is equivalent to invariance because the inclusions are monic.
- `hhomogeneous` uses `Presheaf.IsLocallySurjective` for the represented morphism
  `yoneda.map (ModObj.leftSMul G (V j))` on `Scheme.fppfTopology.over (Spec (.of R))`.
  `ModObj.leftSMul` is exactly `(g,x) ↦ (gx,x)`. Since represented functors are fppf
  sheaves, this is exactly surjectivity as an fppf sheaf morphism, not surjectivity
  on all sections before sheafification.
- The existential field `L`, its `Field` and `Algebra (FractionRing R) L` structures,
  and `FiniteDimensional (FractionRing R) L` are the finite extension. `Algebra R L`
  and `IsScalarTower R (FractionRing R) L` specify the induced base-ring structure.
  They add no restriction: that compatible structure exists uniquely.
- `integralClosure R L` is Mathlib's actual subalgebra of elements integral over R,
  not a chosen model or arbitrary ring. Its Noetherian and integrally closed properties,
  dimension one and finite maximal-ideal set are all explicit conjuncts. Its domain
  structure is inherited from the embedding in the field L.
- `H Y : Over (Spec (.of (integralClosure R L)))`, an existential `GrpObj H`, and an
  existential `ModObj H Y` supply the new group and action. `Smooth`, `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` on both structure maps give exactly the
  two smooth separated finite-type schemes.
- For every field `Ω : Type u` and every `t : Spec (.of Ω) ⟶ Spec (.of (integralClosure R L))`,
  `ConnectedSpace (pullback H.hom t)` states the required connected field fibre. In
  particular arbitrary further field extensions are included, and connected means nonempty.
- `p : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom
  (algebraMap R (integralClosure R L))))).obj X` is precisely a T-morphism to X_T.
  The displayed composite `p.left ≫ pullback.fst ...` is q to the original X.
  `IsIntegralHom`, `Surjective`, and the pointwise `Set.Finite (q ⁻¹' {x})` apply to
  that composite, not just to p. No finiteness of the R-module R' is assumed or asserted.
- For each algebraically closed Ω and t, `U : Fin m → (pullback Y.hom t).Opens`
  supplies finitely many opens. The universal membership clause covers the fibre;
  `Pairwise (fun i j ↦ Disjoint (U i) (U j))` makes the cover disjoint.
- For every algebraically closed E and morphism `c : Spec E ⟶ Spec Ω`, x and y are
  actual points of Y over `c ≫ t`. The displayed a/b equations say that the unique
  corresponding point of Y_Ω lies in `U j`. The final implication and equivalence
  say that, when x belongs to U_j, membership of y in U_j is equivalent to
  `∃ g : Over.mk (c ≫ t) ⟶ H, g • x = y`. This states both invariance and
  transitivity, including after every algebraically closed extension of Ω.
  These are exactly H_Ω(E) and Y_Ω(E) via the fibre-product universal property.

Dependency declarations used (full interfaces and docstrings read):

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `.Hom`.
- def-weil-affine-spectrum: same module, `AlgebraicGeometry.Spec` and `.map`.
- def-weil-pbc-noetherian-ring: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- def-weil-pbc-normal-ring: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`; `IsDomain` is the node's domain specialization.
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, with `QuasiCompact` from the corresponding
  `.QuasiCompact` module, as the recorded conjunction requires.
- def-weil-flat-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.
- def-weil-closed-immersion: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, used through the separated closed-diagonal predicate.
- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- def-pc-fibre-product: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`; `Over.pullback` uses precisely these.
- def-sbc-locally-finite-presentation: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- def-pc-fppf-site: `Mathlib.AlgebraicGeometry.Sites.Fpqc`, `Scheme.fppfTopology`,
  with `Mathlib.CategoryTheory.Sites.Over` for its over-site.
- def-weil-connected-scheme: `Mathlib.Topology.Connected.Basic`, `ConnectedSpace`;
  this is a Mathlib leaf whose mathlib_match needs no Lean-record repair.
- def-weil-finite-integral-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Integral`,
  `AlgebraicGeometry.IsIntegralHom` from the recorded list; the finite branch is not
  substituted for the integral conclusion.

Additional existing Mathlib interfaces are `GrpObj` (Monoidal.Cartesian.Grp),
`ModObj` and `ModObj.leftSMul` (Monoidal.Cartesian.Mod), and
`Presheaf.IsLocallySurjective` (Sites.LocallySurjective). The componentwise normalization,
finite inseparable reduction, integral-closure fibre theorem, regularity, reduction,
smooth fibre criterion, and separated density declarations are plain proof imports,
as are the modules of the Mathlib proof leaves. Four split proof nodes have no
recorded statements yet (finite-equivariant-open-orbits,
semitrait-potential-reduced-normalization, trait-normalization-group-structure,
smooth-group-relative-neutral-open); none is needed to type this statement, and no
unpublished declaration is invented for them.

Edge cases checked before drafting and again against the signature:

- Empty X: `n = 0` and empty Y are permitted; `hcover` imposes no nonemptiness.
- Empty geometric fibre: choose `m = 0`; all orbit assertions are vacuous.
- Empty pieces: no point x satisfies the antecedent, exactly as allowed for empty pieces.
- Generic-only components: there is no surjectivity hypothesis on X.hom or Y.hom;
  flatness does not force a nonempty special fibre.
- The group fibre is nonempty because of its identity, so `ConnectedSpace` has the
  node's correct convention. No connectedness is imposed on Y itself.
- Arbitrary characteristic, noncommutative G, nonreduced input schemes and imperfect
  residue fields are all included. Only H and Y are asserted smooth.
- The common universe u bounds schemes, their test fields and the finite extension;
  it is the project's scheme size convention, not an independent smaller test universe.
  Every field-valued map c is quantified, including identity and arbitrary extensions.
- No excellence, module-finite normalization, or finite morphism q has been added.

Searches made:

1. msearch leanfinder: “An almost homogeneous scheme acted on by a flat group scheme
   over a semilocal Dedekind domain has an integral surjective smooth cover after finite
   fraction field extension”: eight hits, only generic integral/smooth morphism interfaces;
   no such cover theorem.
2. msearch loogle: `GrpObj, MulAction, AlgebraicGeometry.Smooth, integralClosure`:
   zero hits, service says unknown identifier GrpObj. Direct source inspection finds
   the actual categorical GrpObj/ModObj interfaces used above.
3. msearch grep: `GroupScheme|AlmostHomogeneous|openOrbits|smooth.*cover` in AlgebraicGeometry:
   two unrelated SmoothFiber lines, no cover theorem.
4. msearch leansearch: “group scheme action locally homogeneous smooth cover over
   Dedekind domain”: eight hits on smooth morphisms, ideal group actions and manifold
   smoothness; no match.
5. rg of WeilConjectures and Sheaf for `AlmostHomogeneous|almostHomogeneous`, the exact
   proposed name and `almost.homogeneous.*smooth|potential.*smooth.*cover`: no theorem.
   Exact node-id search in WeilConjectures found no declaration. rg of GroupAction,
   GroupScheme and Orbit interfaces found the existing SmoothGroupOrbitGeometry,
   HomogeneousOrbitQuotientGeometry and SchemeActionTorsorGroupoids modules. Their
   statements concern algebraic groups over fields or action-groupoid definitions,
   not this semilocal potential smooth-cover theorem. They demonstrate the shared
   GrpObj/ModObj interface; it is used directly, not duplicated.
6. `dag/lean_names_upstream.json` exact proposed declaration search: no match.

No STATEMENT-DISPUTED flag or node correction is needed. The module docstring records
all ten proof steps for the later proving stage. No theorem is proved in this delivery.

Validation: scompile.py compiled both the sandbox statement and its real library
module against the published live library, with no errors or warnings (31.4 s and
13.7 s reported). Explicit `(C := Scheme.{u})` annotations on the fibre products
resolve the point-type coercions. The node copy changes only `lean`; the recorded
signature is verbatim. All Lean lines are at most 100 characters, all variables and
the universe are explicit, and there is exactly one `sorry` in a named theorem.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
