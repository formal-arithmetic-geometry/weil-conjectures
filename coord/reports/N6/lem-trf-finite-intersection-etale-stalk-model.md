## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteIntersectionEtaleStalkModel` states
`AlgebraicGeometry.finiteIntersection_etale_stalk_model`, with its whole proof
`sorry`. It adds no definitions, instances, axioms, or other theorems. The node
copy changes only `lean`; its accepted mathematical statement and split are kept.
The inherited BLOCKED ending concerned stage 1, not this stage-2 delivery. The
current queue records stage 2 and the node has no existing Lean binding. No
released repair note or current return for this item was present.

Hypothesis and clause correspondence:

- Locally Noetherian scheme: `{X : Scheme.{u}} [IsLocallyNoetherian X]`.
- Nonnegative n and closed D_j: `{n : ℕ}`, `D : Fin n → Scheme.{u}`,
  `i : (j : Fin n) → D j ⟶ X`, `hclosed : ∀ j, IsClosedImmersion (i j)`.
- Subset J of the finite label set: `J : Finset (Fin n)`; `j : J` is a
  selected label, with underlying index `j.val`.
- Z and its canonical i: `c : WidePullbackCone (fun j : J ↦ i j.val)` and
  `hc : IsLimit c`. Thus Z is `c.pt` and i is `c.base`. This is the universal
  property of the finite fibre product, including the base object when J is
  empty. It makes no choice of a new intersection construction. The result
  holds for every representative of this limit, so in particular for the
  existing iterated pullback in `EtaleRegularIntersectionDescent`.
- Closedness and local Noetherianity: the first two conjuncts
  `IsClosedImmersion c.base ∧ IsLocallyNoetherian c.pt`.
- Every affine open U = Spec A': `∀ (U : X.Opens) (hU : IsAffineOpen U)`;
  A' is its canonical coordinate ring `Γ(X, U)` and `hU.fromSpec` is the
  canonical affine parametrization. I'_j is `(i j.val).ker.ideal ⟨U, hU⟩`.
  For a closed immersion this is exactly the ideal in any quotient
  presentation over U (it is the kernel of the structural ring map).
  `⨆ j : J, ...` is the sum of those ideals. The isomorphism `e` identifies
  `pullback c.base hU.fromSpec` with its quotient spectrum and the equation
  with `pullback.snd` states that it is over U. Working in the canonical
  coordinate ring loses no affine presentation: any A' presenting U is
  canonically isomorphic to Γ(U), and its quotient ideal is carried to this
  kernel ideal.
- z, x, chosen chart, A, K, and I: `z : c.pt`, `x = c.base z`, `U`, `hU`,
  `hx : c.base z ∈ U`; A is `X.presheaf.stalk (c.base z)`. The binders K,
  hK, I, hI merely name the finite ideal sum and its extension along the
  germ ring map. They are universally quantified with their defining
  equalities, rather than hidden `let`s or additional mathematical choices.
- Independence of I from U: `I = RingHom.ker (c.base.stalkMap z).hom`.
  The right hand side uses only i and z. This is also the image of the ideal
  sheaf in the local ring, by localization of the affine kernel ideal.
- O_Z,z = A/I: `eA` and its equation on `Ideal.Quotient.mk I a` specify
  the ring equivalence induced by the actual structural stalk map.
- Every étale v and w over x: `∀ W v, Etale v → ∀ w (hw : v w = c.base z)`.
  B is `W.presheaf.stalk w`. φ and hφ specify the actual stalk map with the
  equality-of-points transport; IB and hIB name exactly `I.map φ`.
- B Noetherian and local, and B/IB nonzero, Noetherian and local: the five
  predicates immediately following hIB. `Nontrivial` means nonzero ring.
- Base change to Spec B: the second scheme isomorphism `e` has source
  `pullback c.base (W.fromSpecStalk w ≫ v)` and target `Spec (B ⧸ IB)`;
  its projection equation states that it is over Spec B with its canonical
  quotient structural morphism.
- Unique point over w: existential p, equality hp for the second projection,
  and `∀ p', ... → p' = p`. The equality hz identifies its first projection
  with the original z; this is forced by closed-immersion injectivity.
- Its local ring: `eB : (B ⧸ IB) ≃+* (pullback c.base v).presheaf.stalk p`.
  The equation on each b specifies eB using the actual second-projection
  stalk map and the hp transport, rather than an arbitrary ring isomorphism.
- The natural flat local map A/I → B/IB: q is a ring homomorphism,
  `q.Flat ∧ IsLocalHom q`; its formula on every original a specifies the
  natural quotient of φ uniquely, since the quotient map is surjective.
  The last equation for every a in A/I states that eA and eB carry this q
  to the actual first-projection stalk map, including the hz transport.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  (pqf-def-locnoeth), its affine-cover and stalk interpretation.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (def-weil-closed-immersion).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd` (def-pc-fibre-product),
  exposed by the public algebraic-geometry pullback import. For the finite
  family, Mathlib's `WidePullbackCone`, `.base`, `IsLimit` encode the very
  same universal property, without a second definition.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`
  (def-weil-affine-spectrum), exposed by the public geometry imports.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, `stalkObj`, and `stalkMap`
  (def-weil-pbc-module-stalk) use Mathlib's existing stalk carrier. Here the
  rings O_X,x are those existing scheme structure-presheaf stalks directly;
  there is no module-valued stalk map to rebuild or transport.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (def-weil-etale-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and
  `Flat.stalkMap` (def-weil-flat-morphism); quotient flatness is `RingHom.Flat`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker` and
  `IdealSheafData.ideal` give the canonical affine ideals of the closed
  immersions (the already recorded def-sbc-closed-immersion-ideal-sheaf,
  present among the proof dependencies). This is a public import because
  its notation occurs in the signature; no private ideal-sheaf copy.
- The remaining recorded proof tools are supplied by the plain imports:
  `Sheaf.AlgebraicGeometry.UnramifiedMorphism`, Mathlib's module tilde,
  quotient localization, localization Noetherianity, local-ring quotients,
  and tensor-quotient base change. The corresponding geometry tools are
  already exposed by the geometry imports. The declaration docstring
  records all six proof steps and the matching DAG prerequisites.

Edge cases checked before writing: n = 0 and J empty are valid, since the
wide cospan still contains the base object. Its limiting cone is isomorphic
to X; the empty supremum is the zero ideal and the local quotient map is the
original étale stalk map. No nonempty assumption occurs. Empty X and empty
Z are permitted; the statements about z are vacuous. Empty affine opens
can have zero coordinate rings and are included. In the local clauses the
existence of z and w forces I and IB proper; this is why the nonzero quotient
claim is only there and is not incorrectly asserted for every global affine
quotient. All schemes and their ring stalks use the unrestricted common
universe u; no independent smaller test universe makes a quantifier vacuous.
No characteristic, finiteness, separatedness, or regularity assumption was
added. No statement dispute or source correction was needed.

Searches performed on 2026-10-23 using the prescribed wrapper:

- LeanFinder: "Finite scheme theoretic intersections of closed subschemes
  have quotient stalk rings and etale base changes give flat local quotient
  homomorphisms". Eight hits, including `Flat.stalkMap`, `Flat.of_stalkMap`,
  `Flat.iff_flat_stalkMap`, and algebraic étale tools; none states the whole
  finite-family quotient and canonical stalk comparison.
- Loogle: "AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.Etale".
  No hits.
- Mathlib grep: "intersection.*stalk|stalk.*quotient" in AlgebraicGeometry.
  Five hits, in ProjectiveSpectrum/StructureSheaf, IdealSheaf/Subscheme,
  and ResidueField; none is the asserted multi-clause result.
- LeanSearch: "Finite intersections of closed subschemes of a locally
  Noetherian scheme have quotient stalk rings and etale base change gives
  flat local quotient homomorphisms". Eight hits: local Noetherianity and
  stalk Noetherianity, `Flat.stalkMap`, `flat_iff`, étale locality and flat
  base change. These are components only.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for finite intersections,
  intersection/stalk and stalk/quotient patterns, and the item's id.
  Found `Sheaf.TraceFormula.EtaleRegularIntersectionDescent`: it defines
  iterated intersections and asserts regularity/codimension descent, not
  the present local-model statement. Its proof now depends on this item,
  so it is not imported. The standard limiting-cone formulation avoids
  that import cycle and duplicates none of its helper definitions.
- `rg` in those trees and `dag/lean_names_upstream.json` for the chosen full
  declaration name: no existing declaration.

Read the local Stacks source at the recorded tags, including the affine
closed-immersion characterization, tensor-product affine fibre products,
closed-immersion base change, finite-type Noetherianity and étale base
change. Read the current latest blueprint's lem-trf-local-term-locality
statement/proof and sk-i-curve-zero unit to check the inherited attachment.

Validation: scompile.py compiled the delivered file in module mode both as a
sandbox and under its intended library module name in about 1.8 seconds each,
without errors or unexpected warnings. The first probe needed explicit
`Scheme.{u}` type annotations on the pullback point binders to prevent
ambiguous coercion elaboration; these annotations were added and recompiled.

## Second reading by N6

The dispatcher explicitly prohibits starting another agent, and says that the
maintainer's independent reviewer reads this delivery. This section records a
second pass by this same worker, not a claimed independent review. Reopened
the node statement and the compiled module and matched the hypotheses and
conclusions listed above. Checked both spectrum isomorphisms have projection
compatibility, both local ring equivalences have quotient-map formulas, and
the final comparison uses the first projection with the necessary point
transport. Checked φ and IB are constrained to the canonical stalk map and
extended ideal. Checked the finite ideal supremum and empty family convention.
No mathematical mismatch was found; no node statement was changed. Independent
review remains for the maintainer as specified by the dispatch brief.
