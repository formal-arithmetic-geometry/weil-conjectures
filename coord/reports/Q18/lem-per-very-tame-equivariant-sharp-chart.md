## Worker report

States `AlgebraicGeometry.exists_tame_equivariant_sharp_chart` in
`Sheaf.AlgebraicGeometry.VeryTameEquivariantSharpChart`. Its only theorem has proof
`sorry`; no mathematics is proved. The helper `sharpChartCyclotomicRing` is the
fully defined abbreviation `Localization.Away (n : CyclotomicRing n ℤ ℚ)` for the
coefficient ring already appearing in this node. It uses the existing Mathlib
constructions, has real data, and is listed in `lean.declarations`.

The source PDF was read directly: ILO Exposé VI §3.4, Proposition 3.5(a), and proof
3.7(a), printed pp.74–75. The result uses only conditions (i) and (ii) of §3.1.
There is no statement correction, disputed statement, new independent notion,
or dependency module. The node copy changes only `lean`.

Hypothesis correspondence:

- `X : FineSaturatedLogScheme.{u}` gives the locally Noetherian underlying scheme,
  the actual étale log structure, and étale-local fine saturated charts.
- `{G : Type v} [Group G] [Finite G]` and `a : FSLogGroupAction G X` are the finite
  group and its specified action by log automorphisms. Group size is independent
  of the scheme universe.
- `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and `t : Spec (.of Ω) ⟶ X.scheme`
  are the geometric point, using the recorded inline geometric-point interface.
- `H : Subgroup G` and `_hH` identify H with exactly its geometric stabilizer,
  not a larger ordinary-point stabilizer or an arbitrary subgroup.
- `_htame : IsUnit (Nat.card H : Ω)` says the stabilizer order is invertible.
  The residue field of the strict local ring embeds in Ω. Invertibility of this
  natural integer in either field is equivalent, so this is the exact tame
  condition, also used in the published `FSLogGroupAction.IsTame` definition.
- `_hchar` states triviality on the actual characteristic stalk using all
  pointed relative étale diagrams: associated germs have the same image in
  `Associates`, precisely the quotient by units. This is the identical
  representative-level test used by `FSLogGroupAction.IsVeryTame`, without its
  additional stratum condition. Every germ and its image have such representatives.

Conclusion correspondence, in order:

- `IsFineSaturatedMonoid (X.logStructure.characteristic t)` and
  `∀ q, IsUnit q → q = 1` assert that the actual characteristic Q is fs sharp.
  Multiplicative `1` renders the node's additive `0`.
- `W`, `w`, `b`, `hb`, and `∀ h, w.left ≫ (b h).hom = w.left` give the pointed
  H-equivariant étale neighbourhood: `W` is an object of `X.scheme.Etale`, `w`
  is the chosen lift, `b` is an action by scheme automorphisms, `hb` makes the
  projection equivariant for the given log action's underlying maps, and the
  point is fixed. `IsAffine W.left` selects an affine representative of the
  asserted étale-local chart, allowing its scheme map to an affine target to
  be expressed exactly by a global ring map.
- `β : Q →* M(W)` and `X.logStructure.IsChart W β` give the chart on this
  neighbourhood. This is the recorded associated-log pushout chart condition,
  not merely a homomorphism or a generating map.
- `Associates.mk (germ ... (β q)) = q` is the prescribed identity on the actual
  characteristic at the marked point, with no arbitrary characteristic isomorphism.
- `χ : TensorProduct ℤ (Additive (Abelianization H))
  (Additive (Algebra.GrothendieckGroup Q)) →ₗ[ℤ] Additive (rootsOfUnity n A)`
  is exactly the requested homomorphism from H_ab tensor Q^gp to μ_n(A),
  with `A = strictLocalRing X.scheme t` and `n = Nat.card H`.
  `Abelianization` is Mathlib's quotient by the commutator subgroup, and the
  additive type tags just express the multiplicative groups as Z-modules.
- `ρ : rootsOfUnity n A →* Γ(W.left, ⊤)ˣ` spreads these finitely many roots to
  the neighbourhood; its germ equation is the identity on the entire μ_n(A).
  The equation with `(b h).hom.appTop` fixes every such root. Because `b` fixes
  the point and `hb` relates it to the given action, this also says that the
  original stabilizer fixes μ_n(A), rather than introducing a separate stalk action.
- `unitLift` identifies section-ring units with log units. Its structural-map
  equation makes this the inverse of the given log unit identification; it is
  unique by the log condition. The log-action equation reads precisely
  `h(β q) = unitLift (ρ (χ(h tensor q))) * β q` on the neighbourhood, using the
  given `a.logMap` and its actual section maps, rather than only on ring images.
- `c : Lambda →+* Γ(W.left, ⊤)` and the roots equivalence `e`, together with
  `c(e z) = ρ z`, render the choice of primitive root and the cyclotomic base
  map. Here Lambda is Mathlib's integral cyclotomic ring with n inverted.
  Its group of n-th roots is cyclic of order n; an equivalence of root groups
  therefore takes a primitive root to a primitive root, and the displayed
  equation identifies it with the strict-local choice. In particular n is
  invertible on this affine neighbourhood.
- `d : H →* (Lambda[Q] ≃+* Lambda[Q])` fixes every coefficient `single 1 r`
  and sends `single q 1` to `single q (e (χ(h tensor q)))`. This is the
  required diagonal character action on the actual Mathlib monoid ring.
- `θ : Lambda[Q] →+* Γ(W.left, ⊤)` sends coefficients to `c` and monomials
  to the structural images of `β`. The final equation gives equivariance on
  every ring element. For affine W this is exactly the equivariant scheme
  morphism to `Spec Lambda[Q]`. Its strictness is precisely `IsChart W β`
  for the standard log structure induced by Q. Thus the equivalent strict
  equivariant chart clause is included, not merely mentioned in a docstring.
- The ring is Mathlib's `MonoidAlgebra`, with canonical finite-support basis
  `single q 1`, and multiplication `single q 1 * single q' 1 = single (q*q') 1`.
  This renders both the basis z^q and its multiplication law using the existing
  construction; no redundant tautological conjunct is appended.
- No log regularity, generic freeness, or action on the stratum is assumed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogStructure.characteristic`,
  `EtalePrelogStructure.stalk`, `germ`, `EtaleLogStructure.IsChart`,
  `EtaleLogHom.sectionMap`. The characteristic is literally `Associates` of
  the actual monoid-valued stalk. The module is publicly imported through
  the recorded group-action module.
- `Sheaf.AlgebraicGeometry.FSLogGroupAction`: `FSLogGroupAction`,
  `baseAction`, `logMap`, `base_eq`. Its same geometric tame convention was
  checked, as was the representative formulation in `VeryTameFSLogAction`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField` was
  read to check the recorded geometric-point interface.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, through `X.scheme.Etale`.
- `Sheaf.AlgebraicGeometry.LogRegularPair`: `strictLocalRing`,
  `strictLocalGerm`, `IsFineSaturatedMonoid`, inherited through the fs module.
- Mathlib `Abelianization.of`, `Algebra.GrothendieckGroup.of`, `TensorProduct`,
  `rootsOfUnity`, `CyclotomicRing`, `Localization.Away`, and `MonoidAlgebra`
  provide the standard algebraic constructions directly.

The stated proof dependencies are included as ordinary proof imports:
`FineLogStalkChartSpreading` (`EtaleLogStructure.exists_affine_chart_of_isStalkChart`),
`FsFaceSharpening` (`face_sharpening`), `StrictHenselizationCompatibility`
(`strictHenselizationLocalStructure`), the upstream `StrictLocalRootsOfUnity`
(`Scheme.strict_local_roots_of_unity`), and upstream `Sites.StrictHenselization`
(`Scheme.AffinePointedEtaleNeighborhood.initial_ι`). The fs definition is already
publicly available. `lem-per-tame-unit-extension-character` has no recorded Lean
module in the read repository, so there is no proof import for it; the complete
natural-language proof plan retains that exact DAG dependency. It is not needed
to type this statement. All recorded proof-dependency declarations and their
source docstrings were inspected.

Edge cases checked before finalizing:

- Trivial stabilizer: n = 1, μ_1 is trivial and Lambda is Z, so the character
  and diagonal action are trivial. No assumption n > 1 or faithful action occurs.
- Trivial log structure: Q is the one-element monoid; the characteristic
  identification and tensor pairing remain meaningful, and Lambda[Q] = Lambda.
- Nonabelian H: only its abelianization enters the pairing; the action and
  stabilizer remain the full H, with no abelianness hypothesis.
- Positive characteristic dividing n is excluded exactly by `_htame`;
  characteristic zero and all prime-to-characteristic orders are included.
- Nilpotent or non-log-regular X is allowed. No structural-map injectivity is
  imposed on the log structure, and the eigenvector equation is in log sections.
- Empty X has no geometric point t, so the universally quantified assertion
  has its intended vacuous interpretation.
- Different group and scheme universes are retained; all geometric objects
  use the scheme universe consistently with the published dependencies.

Searches for existing declarations (2026-10-24):

- `msearch.py ... leanfinder "A tame finite stabilizer acting trivially on the
  characteristic monoid of an fs log scheme admits a roots of unity equivariant
  sharp chart"`: eight unrelated number-field stabilizer results; no match.
- `msearch.py ... loogle "Abelianization.of, rootsOfUnity, TensorProduct.tmul"`:
  zero hits for that combined search. The individual constructions are used
  directly from their Mathlib source declarations.
- `msearch.py ... grep "equivariant.*chart|sharp.*chart|logarithmic"
  AlgebraicGeometry`: one unrelated elliptic-curve logarithmic-height hit.
- `msearch.py ... leansearch "fine saturated logarithmic scheme equivariant
  chart tame group action"`: eight unrelated general scheme/action results;
  no fs equivariant chart theorem.
- `rg` in `lean/WeilConjectures` for the node id and
  `equivariant.*chart|sharp.*chart`: no matching theorem, only an unrelated
  comment in AffineAlgebraReductionsCartesian. The requested literal node-id
  search was also made with the same no-match result.
- `rg` in `lean/Sheaf` finds the ordinary log-regular sharp chart and very-tame
  definitions, but no equivariant sharp-chart theorem. The former assumes log
  regularity and gives no character or equivariance, so is not an existing match.
- `rg` across Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for the new
  declaration names finds no collision. CyclotomicRing and localization sources
  were read and used, rather than introducing another cyclotomic-ring construction.

Validation: the module compiled with the required `scompile.py` server wrapper,
without errors or unexpected warnings. Dry-run and final-delivery results are
recorded below after the gate runs. No local/global Lake build, direct Git
operation, source-library write, or launcher-script modification was performed.

Delivery gate: `deliver2.py Q18 lem-per-very-tame-equivariant-sharp-chart --no-push`
printed `OK (dry run): commit 3ae650a7a79 passes the preflight and compiles; nothing pushed`.
The staged packet consists exactly of this node, its single module, and this report.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
