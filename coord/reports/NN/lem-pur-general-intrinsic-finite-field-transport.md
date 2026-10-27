## Worker report

This is an existing-declaration attachment. No Lean module is added, and only the item's
`lean` field changes. The main declaration is
`WeilConjectures.SfAlgebraicallyClosedCoefficients.shift_existsUnique`, in
`Sheaf.Paper.SfAlgebraicallyClosedCoefficients`. Its companion declarations, listed in
`lean.declarations`, together state all the item's clauses. This is a stage-2 attachment,
not a claim that the existing construction is sorry-free.

I read the current node, including its retained source note and all eight proof steps;
the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/_section.md`;
and the existing intrinsic construction in
`lean/Sheaf/Paper/SfAlgebraicallyClosedCoefficients.lean`, particularly lines 575–1303.
The blueprint's current unit presents descent as a two-colimit; the more detailed intrinsic
pair implementation retained by this node is exactly the construction in that module.
`scompile.py --source Sheaf.Paper.SfAlgebraicallyClosedCoefficients` confirmed the current
server module and the same public interfaces. All names below, unless qualified otherwise,
are in `WeilConjectures.SfAlgebraicallyClosedCoefficients`.

The hypothesis and clause correspondence is as follows.

| Node hypothesis or clause | Existing Lean rendering and location |
|---|---|
| Global datum `(p,a,q,k₀,k)` | `D : FiniteFieldDatum.{d}`; `FiniteFieldDatum` in `Sheaf.Paper.FiniteFieldFiber` supplies primality, positive exponent, `q = p ^ a`, the finite base field and its algebraic closure. The intrinsic module's parameter block is at lines 575–577. |
| Prime `l ≠ p` | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` in that block and the explicitly bound companion theorems. |
| Arbitrary algebraic closure of `Padic l` | `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`. This permits every fixed closure, rather than only the built-in `AlgebraicClosure`. |
| Any scheme, with independent universe and no map to `k` | `(Y : AlgebraicGeometry.Scheme.{u})`; `u`, `v`, `d` are separate universe variables. There is no `Over`, finite type, nonemptiness, separatedness or invertibility binder on `Y`. |
| Directed finite coefficient fields | `AlgebraicallyClosedCoefficients.Index l Ω = Padic.FiniteCoefficientFields l Ω`. `Common A B` retains both lower-bound proofs, and `commonNonempty`/`commonDirected` use the compositum. |
| The same prescribed small models and inclusions | `AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E = Shrink.{u} E.val`, with `coefficientSmall` from the finite-basis coordinate equivalence. `coefficientInclusion` conjugates `IntermediateField.inclusion h` by the two `Shrink.algEquiv`s; `coefficientInclusion_laws` gives actual algebra-hom identity/composition. Read at lines 223–266 of `Sheaf.Paper.AlgebraicallyClosedCoefficients`. |
| Full intrinsic integral category, derived complete with constructible reductions in one uniform finite interval | `sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y`, from `Sheaf.Paper.SfIntegralConstructible`. Its defining predicate is `IsSfDerivedComplete ∧ ∃ a b, a ≤ b ∧ ∀ n, intrinsicFiniteTorsionConstructible ... ∧ support ⊆ Set.Icc a b`. The same `a,b` serve all positive reduction levels. |
| Raw rationalization, induced shifts and integral-image triangles | `Stage D l hl Ω Y E` at lines 581–582 is `D.sfRationalCategory l hl (Coefficient ... E) Y`, the abbreviation for `sfRationalConstructibleCategory`. `Sheaf.Paper.SfRationalizationKaroubi` defines this as `ScalarLocalization` of that intrinsic integral category at its actual uniformizer. `stageShift`, `stagePretriangulated`, `stageTriangulated` use its induced structures; no Karoubi envelope is present. |
| Actual scalar functor with proof parameter `(p,hl)` and tensor constraints | `transition E L h` at lines 629–633 is `sfRationalScalarExtension ... D.p hl ... (coefficientInclusion ...)`. `associator` at lines 751–759 is `sfRationalScalarComp` followed by the equality of the actual conjugated inclusions; `unitor` at lines 763–768 uses the inclusion identity and `sfRationalScalarUnit`. |
| Normalized published stage system and literal pairs/inclusions | `stageSystem_existsUnique` at lines 808–821 specifies precisely these functors and associators. `stageSystem`, `Pair`, `inclusion` are its chosen system, `PairCategory`, and `StageSystem.ι`, not an arbitrary equivalent category. |
| Unique ordinary-to-completed normalized integral comparison | `integralTransitionCommShift_existsUnique` at lines 646–673 is `∃! c : (sfConstructibleIntegralScalarExtension ...).CommShift ℤ, ...`. Its equation for every `n,K` is exactly the image under the fully faithful intrinsic inclusion followed by its comparison, equal to the conjugated ordinary comparison. `integralTransitionCommShift` chooses that uniquely specified object. |
| Unique integral-image-normalized rational comparison, all integers | `transitionCommShift_existsUnique` at lines 704–713 is uniqueness of the entire `CommShift ℤ`, normalized at degree one by localization of the integral comparison on `K.obj`. `transitionCommShift` is its chosen structure. This is not merely a degree-one existence assertion. |
| Transport this precise comparison, exactness and additivity to published transitions | `stageTransitionCommShift` at lines 835–841 is `cast` along the equality given by `stageSystem_existsUnique`. `stageTransition_exact` and `stageTransition_additive` at lines 848–873 apply to those actual transitions. `transitionExact` uses the selected normalized comparison and `transitionAdditive` uses the published scalar functor. |
| Actual associator-conjugated transport formula | `transport A B L M h f` at lines 904–909 is `(assoc ...).inv.app A.obj ≫ stageTransition.map f ≫ (assoc ...).hom.app B.obj`, the displayed formula in Lean's left-to-right composition notation. |
| Additive transport, reflexive identity, composition, including repeated fields | `transport_additive` at lines 916–929 gives preservation of zero and addition; `transportHom` bundles the same map as an additive homomorphism. `transportSystem` at lines 945–960 is `DirectedSystem (StageHom A B) ...`, whose fields are identity and composition. It explicitly handles reflexive transport using the normalized unitor and faithfulness. |
| Actual abelian-group Hom colimits | `ColimitHom A B` at lines 968–970 is `AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)`, with `colimitOf` the actual structure maps. `homCoordinates_existsUnique` at lines 988–998 fixes the unique equivalence by `e (PairCategory.mkHom L hA hB f) = colimitOf A B L hA hB f`. `homAddCommGroup` is precisely the transfer through that chosen equivalence. |
| Unique full coherent shift structure | `shift_existsUnique` at lines 1153–1172 quantifies `∃! s : HasShift (Pair D l hl Ω Y) ℤ`. Uniqueness is equality of the full structure, with its zero and addition coherence, rather than only object maps. |
| Literal object shift `(E,K) ↦ (E,K[n])` | The second conjunct of `shift_existsUnique` says `shiftFunctor.obj A = shiftPair n A`; `shiftPair` at lines 1128–1129 is the literal pair `⟨A.stage, shiftFunctor.obj A.obj⟩`. |
| Representative shift formula with the selected sigma | The third conjunct is `HEq` of the shifted `ofHom` with `ofHom ... (shiftRepresentative ...)`. `shiftRepresentative` at lines 1133–1140 is `sigma_source.hom ≫ shiftFunctor.map f ≫ sigma_target.inv`, exactly the displayed formula. `HEq` records the displayed object equalities without adding extra assumptions. |
| Identity-normalized coherent inclusion comparisons | The last conjunct of `shift_existsUnique` supplies `∀ E, (inclusion E).CommShift ℤ` with hom components `HEq ... (𝟙 ...)` for every integer and object. `inclusionCommShift` chooses these constrained comparisons. |
| Additive pair shifts and inclusions | The first conjunct of `shift_existsUnique` and `shiftAdditive` give additivity for every integer. `inclusion_additive` at lines 1086–1099 gives additivity for each actual `inclusion`. |
| Canonical stage identifications commute with the comparisons | `transitionIso_commShift` at lines 1211–1219 is `NatTrans.CommShift ((stageSystem ...).transIso h).hom ℤ`, using the already selected transition and inclusion instances. The existing `transIso` is fixed by the associator representative, not newly chosen. |
| Bilinear composition in the original pair category | `composition_bilinear` at lines 1048–1064 gives both `(f+f') ≫ g` and `f ≫ (g+g')` equations. `preadditive` uses `homAddCommGroup` for its Hom data and these same composition equations. |
| Zero pair | `zero_exists` at lines 1193–1202 gives `HasZeroObject (Pair ...)`; its actual witness is `(inclusion (Padic.finiteCoefficientBase l Ω)).obj (0 : Stage ... _)`. The canonical bottom-stage pair is retained, as its definition/proof shows. |
| Finite representatives and eventual equality | `representatives` at lines 1108–1124 exposes representatives using `ofHom`, and equivalence with equality of the actual transports at one later common field. This also confirms that the coordinate and representative language concerns the original quotient Hom. |
| Common-stage predicate and Verdier structure | `Distinguished` at lines 1224–1225 is precisely `stageSystem.CommonStageDistinguished`. `pretriangulated`, `isTriangulated`, `inclusion_exact` at lines 1229–1241 are the specified common-stage Verdier structure and exact inclusions. `distinguished_iff` at lines 1247–1256 equates the distinguished set with that actual predicate, including TR4 via `isTriangulated`. |
| Cone with literal third pair `(L,C)` | `commonStage_cone` at lines 1269–1276 says the actual `stageSystem.commonStageCone A B L ... C u i p` is distinguished for any given distinguished stage cone. Its definition in `Sheaf.CategoryTheory.StageSystemCommonStageCones` is `Triangle.mk (mkHom ... u) (delta_B.hom ≫ j_L.map i) (j_L.map p ≫ beta.hom ≫ shiftFunctor.map delta_A.inv)`. The third object is literally `j_L.obj C = ⟨L,C⟩`. Its source proof explicitly uses `Triangle.isoMk` with the two canonical `isoToStage` maps and `Iso.refl` on this third pair. |

Every statement-dependency record was read, and its recorded source declaration and docstring
were opened, including the Mathlib leaves. The dependency interfaces used are:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Mathlib.NumberTheory.Padics.PadicNumbers`: `Padic`; and
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure` (also read the recorded
  `AlgebraicClosure` match). These are the coefficient field and closure binders.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`,
  `finiteCoefficientCompositum`, `finiteCoefficientBase`, `finiteCoefficientFields_properties`.
- `Sheaf.Paper.AlgebraicallyClosedCoefficients`:
  `WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient`, `coefficientInclusion`,
  `coefficientInclusion_laws`; only its coefficient transport is used, not its legacy stages.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `WeilConjectures.sfRationalConstructibleCategory`,
  its induced shift/triangulation declarations, and `sfRationalScalarExtension`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages`:
  `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique`,
  `specialization_transition`, `specialization_transitionShift`; these specify the datum-free
  system and identify its normalized transitions with the finite-field realization.
- `Sheaf.CategoryTheory.ExactStagePairData`:
  `CategoryTheory.StageSystem.ExactStagePairData`; its underlying pair, comparison,
  triangle image and predicate constructions reuse `StageSystem.PairCategory`, `ι`,
  `transIso`, `isoToStage`, `Functor.mapTriangle` and `CommonStageDistinguished`.
- `Sheaf.Paper.SfAlgebraicallyClosedCoefficients`: the two recorded route normalization
  theorems, `integralTransitionCommShift_existsUnique` and `transitionCommShift_existsUnique`.
- `Mathlib.Algebra.Colimit.Module`: `AddCommGroup.DirectLimit`, `DirectLimit.of`,
  `DirectLimit.lift`, and the directed-system identity/composition interpretation.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`, `.Functor`:
  `CategoryTheory.Pretriangulated`, `IsTriangulated`, and `Functor.IsTriangulated`.

The four datum-free proof-dependency nodes (specialization-pairs, pair-Hom coordinates,
pair-shift normalization, and transition-shift compatibility) currently have no `lean`
record or Mathlib match. Their statements were read. They do not obstruct this attachment:
the finite-field versions requested here are already stated directly in the existing module;
no new proof or dependency module is needed. The accepted split and all dependency lists stay
unchanged. In particular there is no attempt to manufacture a second shift interface or wait
on an unstated proof prerequisite.

Edge cases checked in the signatures and definitions: empty `Y`; independent `d,u,v`;
`E = L`, `L = M`, and all repeated-field transports; zero morphisms and the zero pair;
all `n : ℤ`, including zero and negative integers; the bottom coefficient field; arbitrary
algebraic closures, not just one model. No edge case requires a finite-type or finite-field
structure on `Y`. No statement correction, disputed statement, new node or dependency repair
is needed.

Searches actually run with `msearch.py NN lem-pur-general-intrinsic-finite-field-transport`:

- `leanfinder`: "Normalized intrinsic finite field scalar stage shifts representative Hom
  transport colimit triangulated pair category". Eight general triangulated-category hits;
  none is the specific intrinsic finite-field interface.
- `loogle`: `Functor.CommShift, HasShift`. Zero hits, with diagnostic
  `unknown identifier 'Functor.CommShift'`; this is not evidence that the project has no match.
- `grep`, in Mathlib `CategoryTheory`:
  `shift_existsUnique|transportSystem|homCoordinates_existsUnique`. Zero matches.
- `leansearch`: "finite coefficient field scalar extension normalized shifts directed colimit
  Hom triangulated pair category". Eight hits including `CategoryTheory.IsTriangulated`,
  field direct limits, T-structures and derived-category triangulation; no exact specialization.
- Local `rg` over both `lean/WeilConjectures` and `lean/Sheaf` and
  `dag/lean_names_upstream.json` for
  `intrinsic-finite-field-transport|shift_existsUnique|homCoordinates_existsUnique|transportSystem`.
  This found the exact intrinsic finite-field collection in
  `Sheaf.Paper.SfAlgebraicallyClosedCoefficients`, its datum-free counterparts, and the older
  legacy collection. Reading the signatures distinguished these presentations.
- `grep -rn 'lem-pur-general-intrinsic-finite-field-transport' lean/WeilConjectures`:
  no occurrence. The match is in the existing `Sheaf` module, not a same-named upstream theorem.

Validation: `deliver2.py --no-push` compiles server module-mode `#check` probes for every
attached declaration through `scompile.py`, then runs the server preflight. No local Lean
compiler or global build is used. The packet contains only this report and the item's node
with its `lean` record; there is no new theorem proof or new definition.

## Second reading by NN

This is the author's second reading; no second agent was started. The maintainer supplies
the independent review. I reopened the node and the recorded shift signature, checked each
clause in the table against the actual construction, and checked the raw rational stage
abbreviation through `FiniteFieldDatum.sfRationalCategory`. The important distinctions are
that `SfAlgebraicallyClosedCoefficients.Stage` uses the current intrinsic integral predicate,
that its rational category has no idempotent completion, and that its shift uniqueness is
`∃! s : HasShift ... ℤ` with identity-constrained inclusion comparisons. The similarly named
legacy `AlgebraicallyClosedCoefficients` category does not provide this attachment.

I also checked the two normalization equations, the equality `cast` defining the published
transition comparison, the direct-limit transfer defining Hom addition, and all three cone
arrows. The cone uses `isoToStage` and the already fixed inclusion comparison; its third
object is the literal pair and is not replaced by an isomorphic representative. These checks
found no mismatch requiring a statement or dependency change. The existing declarations still
contain postponed proofs, which is permitted for a stage-2 record and is explicitly disclosed.
