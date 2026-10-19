## Worker report

This delivery states `AlgebraicGeometry.exists_equivariant_sharp_chart` in
`Sheaf.AlgebraicGeometry.VeryTameEquivariantSharpChart`. Its proof is `sorry`, as required
for stage 2. The two item-owned auxiliary declarations are the explicit abbreviation
`SharpChartCyclotomicRing` and the witness structure `EquivariantSharpChart`; neither
chooses data from a postponed existence theorem. Every universe and variable is bound,
and `autoImplicit` is disabled. There are no new DAG nodes or dependency modules.

I read ILO, Exposé VI §3.4, Proposition 3.5(a) and proof 3.7(a), printed pp.74--75,
from the supplied PDF, and the reviewed four-step DAG proof. The earlier worker's
stale-dispatch reason concerned Q131's stage-1 split, which is already merged. That
split has no `lean` or `reviewed_lean` record. This delivery preserves its statement,
proof and review; it supplies the still-missing stage-2 declaration. The retained
sandbox contained only dispatcher brief markers, with no interrupted delivery packet.

Hypotheses, matched individually:

- The locally Noetherian fs log scheme `(X,M)` is `X : FineSaturatedLogScheme.{u}`.
  Its `scheme`, `locallyNoetherian`, `logStructure`, and `fineSaturated` fields are
  exactly the existing dependency interface, not an extra divisorial assumption.
- The finite group acting on the entire log scheme is `G : Type v`, `[Group G]`,
  `[Finite G]`, and `a : FSLogGroupAction G X`. The action includes the prescribed
  scheme action, log maps, their compatibility, identity and multiplication laws.
  I add the already landed definition node `def-per-fs-log-group-action` to stmt_deps,
  as permitted for a landed notion, and import its existing module. No action is copied.
- The geometric point is `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`,
  `t : Spec (.of Ω) ⟶ X.scheme`, exactly the recorded geometric-point convention.
- The stabilizer is `H : Subgroup G` with
  `hH : ∀ g, g ∈ H ↔ t ≫ (a.baseAction g).hom = t`.
  Thus H is required to be the full geometric stabilizer, not any smaller subgroup.
  Giving the subgroup with its defining equality is a presentation of the object H
  in the node, not an additional hypothesis on the action.
- `A` is the existing `strictLocalRing X.scheme t`, the ring-valued étale point fibre.
  `Q` is the existing `X.logStructure.characteristic t`, the actual `Associates`
  quotient of the monoid-valued étale stalk, with units identified through the existing
  log unit condition. Neither an arbitrary local ring nor an abstract isomorphic
  characteristic monoid is substituted.
- `n=|H|` is written `Nat.card H` throughout. The premise is
  `htame : IsUnit (Nat.card H : Ω)`. This is equivalent to invertibility in the
  residue field of A: that residue field embeds into Ω, and both fields have the
  same characteristic. It adds no algebraic closure assumption on that residue field.
- Triviality of H on Q is `hcharacteristic`. For every relative pointed étale diagram
  `(U,p)`, `(V,q)`, `k : V.left ⟶ U.left` with
  `hk : k ≫ U.hom = V.hom ≫ (a.logMap h.val).base` and
  `q.left ≫ k = p.left`, it equates the `Associates.mk` classes of the log action's
  section map and the original section germ. This tests exactly the induced action
  on the geometric characteristic. All stalk elements are section germs. The test is
  nonvacuous for every pointed neighbourhood: rebase its structure map by the inverse
  base automorphism, retain its lift using that h fixes t, and take the identity on
  its underlying scheme for k. Naturality in `EtaleLogHom` identifies all such diagrams.

Conclusions, matched individually:

- `Nonempty (EquivariantSharpChart X a H t)` supplies the chart data, rather than
  assuming a chart or diagonalization as an input.
- `fineSaturated` and `sharp` assert that the actual Q is fs and that its only unit
  is 1. The monoids in the imported log interfaces are written multiplicatively,
  so 1 is exactly the additive zero in the informal node.
- `W : X.scheme.Etale` and `point : (Scheme.pointSmallEtale t).fiber.obj W` give an
  actual pointed étale neighbourhood, not an open subset of a replacement stalk.
  `action : H →* Aut W.left`, `point_fixed`, and `action_over` make it an
  H-equivariant pointed neighbourhood over the original action.
- `chart : Q →* M(W)` and `isChart` use the existing all-geometric-stalk pushout chart
  predicate. `characteristic_identity` says `Associates.mk (germ (chart q)) = q` for
  every q, preserving the specified identification with the original characteristic.
- `character` has domain
  `TensorProduct ℤ (Additive (Abelianization H))
    (Additive (Algebra.GrothendieckGroup Q))`
  and codomain `Additive (rootsOfUnity (Nat.card H) A)`. It is an additive group
  homomorphism, exactly the homomorphism between the corresponding abelian groups
  in the node. `Abelianization` is the quotient by the commutator subgroup, and
  `GrothendieckGroup` is the existing actual group completion.
- `eigenvector` is an equality of log sections for every h and q. Its unit witness z
  maps under the log structural map to the cyclotomic character scalar, and the given
  action's `sectionMap` sends `chart q` to `z.val * chart q`. The log unit condition
  identifies z with that ring unit; no injectivity of the full structural map is
  assumed. `character_germ` identifies these coefficient characters with `character`
  through the canonical `strictLocalGerm`, on every element of the tensor product.
  Therefore this is exactly `h(a(q))=χ_q(h)a(q)`, also at the marked stalk.
- The theorem's second conjunct asserts fixedness of every strict-local nth root
  using every representative r and every pointed relative diagram. Its premise is
  `(strictLocalGerm ... r)^Nat.card H = 1` and its conclusion identifies the germ of
  `k.appTop r` with the original germ. Positive n makes all such roots units. Every
  strict-local element is represented by a section, so this states fixedness of the
  whole μ_n(A), not merely the image of the chosen pairing.
- The cyclotomic coefficient ring is explicitly
  `ULift.{u} (Localization.Away (n : CyclotomicRing n ℤ ℚ))`, exactly
  `Z[zeta_n,1/n]`, with only a universe lift. `coefficient` gives its ring map to
  regular functions on W; this is the étale-local choice of a primitive root.
  `coefficient_fixed` makes the action on this base ring trivial.
  `cyclotomicCharacter` gives the pairing in its roots of unity and `character_germ`
  specializes it to A. This is the same character, not an unrelated second pairing.
- `modelAction` is the action on `Spec Λ[Q]`. `model_diagonal` specifies its pullback
  on EVERY `MonoidAlgebra.single q c`, multiplying its coefficient by χ_q(h).
  These are Mathlib's actual finitely supported monoid-algebra basis elements;
  their product is `single (q*r) (c*d)`, hence `z^q z^r=z^(q+r)` in additive notation.
- `toModel_eq` pins `toModel` to the Γ--Spec adjunction applied to
  `MonoidAlgebra.liftNCRingHom coefficient (alpha.comp chart)`.
  Thus it is the canonical scheme morphism induced by these precise sections, not
  an arbitrary map. `isChart` makes that morphism strict for the standard Q-log
  structure on the model, and `equivariant` states the actual equation of scheme
  morphisms. Together with the log-section eigenvector equation this is the strict
  equivariant chart of VI §3.4.
- No regularity of X, admissibility, quotient, generic freeness, trivial action on
  the stratum, or residue-field identification was added.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogStructure.IsChart`,
  `EtaleLogStructure.characteristic`, `EtalePrelogStructure.germ`, and
  `EtaleLogHom.sectionMap`. I read their full signatures and docstrings.
- `Sheaf.AlgebraicGeometry.FSLogGroupAction`: `FSLogGroupAction`, including all
  fields and its source docstrings; its node and recorded declaration were read.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; and
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`, read with
  its full signature and the recorded inline geometric-point convention.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` and `Scheme.Etale`;
  the full class definition and the site's object definition were read.
- The proof imports the stated proof dependencies
  `Sheaf.TraceFormula.FsFaceSharpening` (`face_sharpening`),
  `Sheaf.AlgebraicGeometry.FineLogStalkChartSpreading`
  (`EtaleLogStructure.exists_affine_chart_of_isStalkChart`),
  `Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity`
  (`Scheme.strict_local_roots_of_unity`),
  `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`
  (`strictHenselizationLocalStructure`), and
  `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`
  (`Scheme.AffinePointedEtaleNeighborhood.initial_ι`). Their statements and source
  modules were inspected. The unit-extension character proof node is not yet stated;
  its statement is read and its id appears in the theorem's complete proof docstring.
  Its eventual import is maintainer bookkeeping, not a required object in this statement.

Searches made:

- `msearch.py`, LeanFinder: "A tame stabilizer acting trivially on the characteristic
  monoid of a fine saturated log scheme admits an equivariant sharp chart with roots
  of unity characters". Eight hits concern number-field stabilizers and infinite-place
  ramification. Reading the returned types found no logarithmic chart statement.
- `msearch.py`, Loogle: `"LogStructure"`. Zero hits.
- `msearch.py`, grep: `Equivariant.*Chart|LogStructure|LogScheme` in
  `Mathlib/AlgebraicGeometry`. Zero hits.
- `msearch.py`, LeanSearch: "Finite group action on fine saturated log scheme admits
  sharp equivariant chart with diagonal characters". Eight hits concern properly
  discontinuous actions, ordinary equivariance, representations and orbit quotients.
  No hit has a log structure or this chart conclusion.
- `rg` in upstream `WeilConjectures` for the item id and logarithmic action/chart names:
  no exact statement. The same search in project `lean/Sheaf` found only downstream
  proof docstring citations, not a statement of this lemma.
- Project source searches found the existing `FSLogGroupAction`, which is reused;
  the divisorial-action interface is a narrower notion and is not substituted here.
  The nonequivariant `exists_sharp_chart_of_logRegular` imposes log regularity, so it
  is not this statement. `GabberFixedLocus.LocalChart` concerns a different and much
  larger downstream local model and its additional hypotheses; it is not reused as
  an assumption or imported backwards.
- DAG and source searches for cyclotomic localization, `EquivariantSharpChart`,
  `SharpChartCyclotomicRing`, the item name and its proposed theorem name found no
  duplicate. `tools/blueprint_refs.py search 'equivariant sharp chart'` found no unit
  binding under that phrase. The existing item node itself is retained, not split again.

Edge cases checked:

- H trivial: `Nat.card H=1`, μ_1 is trivial, and the character and model action
  reduce to the ordinary sharp chart with coefficient ring Z. The H-action on W
  includes no freeness or faithfulness condition.
- Q trivial: the tensor's second factor is zero, the character is trivial, and
  `MonoidAlgebra Λ Q` is Λ. The chart assertion still includes the full log unit
  condition and does not require any nonunit section.
- Characteristic zero and positive characteristic prime to |H| both satisfy the
  same unit premise; wild stabilizers are excluded exactly as in the node.
- G may be nonabelian: only the character factors through `Abelianization H`;
  neither H nor G is required abelian, and H need not be normal.
- The ambient scheme is not assumed affine, connected, regular or nonempty.
  When a geometric point t is supplied the relevant component is nonempty; for
  the empty scheme there is no t, so the universally quantified theorem is vacuous.
- The group universe v is independent of scheme universe u. The tensor product
  retains the resulting maximum universe; no equality of universes is imposed.
- Log structures with noninjective alpha and nonreduced schemes are retained:
  equivariance is an equality of log sections, not just of their structural images.

No statement correction or dispute was necessary. The existing statement is unchanged.
`scompile.py` compiled both the sandbox and library views of the single delivered
module cleanly under its ordinary per-file 60-second limit (14.4 s and 13.2 s), with
no errors or warnings. The only theorem has the required postponed proof.

## Second reading by Q77

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
