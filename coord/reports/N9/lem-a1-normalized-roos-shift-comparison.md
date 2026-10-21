## Worker report

Item: `lem-a1-normalized-roos-shift-comparison`, group N9, 2026-10-21.

The module `Sheaf.CategoryTheory.NormalizedRoosShiftComparison` states
`CategoryTheory.normalizedRoosShiftComparison`, with `sorry` as its entire proof.
It defines no replacement cone, module category, derived category, limit, inclusion,
or comparison. There are no new nodes, dependency repairs, or statement corrections.
The existing landed definition node `def-weil-strict-roos-model` is added to
`stmt_deps` because its actual constructions occur in the signature; it was already
an explicit proof dependency. The natural index n represents positive index n+1.

Hypotheses and clauses, read against the node:

| Node text | Lean rendering |
| --- | --- |
| A small site C | `{C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)`; the coefficient/module universe is `max uC vC t`, containing both site universes. No equality of site object and morphism universes is imposed. |
| A sheaf R of commutative rings | `R : Sheaf J RingCat.{max uC vC t}` and `_hcomm : ∀ U a b, a*b=b*a`; this is the dependency's forgetful encoding of commutative ring sheaves. |
| A=Mod(R), with its abelian category structure | The dependency's `ringedSiteModules.{max uC vC t} R`, transparently Mathlib `SheafOfModules`; `HasSheafify` and `WEqualsLocallyBijective` provide its canonical abelian structure on a small site. |
| Exact countable products | `HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules … R)`. |
| Ordinary unbounded derived categories of A and strict towers | The two `HasDerivedCategory.{w}` binders and `DerivedCategory.{w}`; strict towers are `ℕᵒᵖ ⥤ ringedSiteModules … R`. All complex degrees and shifts range over ℤ. |
| Rlim computed by K-injective resolutions and termwise limit | `RF`, `η : roosLimitFunctor ⋙ Q ⟶ Q ⋙ RF`, and `_hRF : RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso …)` specify total right derived inverse limit. The last conclusion computes its shift on every supplied K-injective resolution. |
| Precisely the normalized comparison rho | `CF`, `κ : roosF ⋙ Q ≅ Q ⋙ CF`, `ρ : CF ≅ RF`, and `_hnorm : ∀ X, Q.map (roosι X) ≫ κ.hom.app X ≫ ρ.hom.app (Q.obj X) = η.app X`. This equation is the normalized inclusion/unit characterization of the comparison in `strictRoosComparison` and `strictRoosNormalization`. It specifies the named map, not a new assumption about the site or towers. For a resolution q it recovers exactly `Q(roosF.map q)` followed by the inverse localized inclusion and the unit-normalized derived-limit identification. |
| The cone C(X)=Cone(1-s)[-1] and its differential | `roosF` from `StrictRoosModel`, whose object is exactly that shifted cone; its `roosU` is the recorded transition endomorphism. `roosχ` provides the node's `(y,x)` order, with differential `(-dy-(1-s)x,dx)`. No arbitrary cone replacement is used. |
| For every r, sigmaC is the chain isomorphism `(y,x) ↦ ((-1)^r y,x)` | Existential `cC : roosF.CommShift ℤ`. Its natural isomorphism is characterized by the first conjunction, for every X,r,q,n. The `roosProj` equation fixes x, and the `mappingCocone.snd` equation multiplies y by `r.negOnePow`, after canonical degree-shift and level projections. Products and the two cone projections jointly determine the map, so these are the full coordinate formula. The inverse has the same sign under the reversed termwise identifications because the sign squares to 1. |
| These are coherent termwise shifts | `Functor.CommShift` contains the zero and shift-addition laws, as well as natural isomorphisms. |
| The chain shift descends to the derived Roos functor | `cD : CF.CommShift ℤ` and the second conjunction identify its comparison with `Q(sigmaC)` through κ and the canonical `Q.commShiftIso`; no independent derived shift is substituted. |
| The displayed square `sigmaLim rho = rho[r] sigmaC` | The third conjunction, `∀ N r, ρ.hom.app (N⟦r⟧) ≫ sigmaRF = sigmaCF ≫ (ρ.hom.app N)⟦r⟧'`. Lean composition is left-to-right. N ranges over the entire derived strict-tower category, not only chosen complexes. |
| SigmaLim is represented by shifting a K-injective resolution and the identity on compatible limit tuples | `cL : roosLimitFunctor.CommShift ℤ` is fixed by the fourth conjunction, whose component equation says its nth limit projection in degree q is the original projection in degree q+r. In the last conjunction, q:X→I is any quasi-isomorphism with I K-injective; `d` and `ds` identify the actual limits of I and I[r] with RF(QX) and RF(Q(X[r])). Their unit equations pin these identifications uniquely. The last equation transports the termwise limit shift through exactly these identifications and the canonical localization shift. |
| Inclusion `(0,z)` retains its normalization under shifts | The fifth conjunction is the actual chain-map identity `roosι (I⟦r⟧) ≫ sigmaC = sigmaL ≫ (roosι I)⟦r⟧'` for K-injective I. `roosι_χ` of the existing model fixes its coordinates to `(0,z)`. |
| Equality is natural for all derived morphisms | cD and cR are natural isomorphisms on the whole derived category; rho is one natural isomorphism, and the square is stated for every derived object. Thus the same square intertwines every derived morphism, including inverses of quasi-isomorphisms. |
| Independent of resolution | The same cR satisfies the representative equation for every X,I,q. Neither injective terms nor a particular resolution functor are imposed. The d and ds maps are unique: RF(Qq) and RF(Q(q[r])) are isomorphisms and their composites are fixed to η. This also covers alternative resolutions without injective terms. |
| Coherent for zero and integer addition | Each of cC,cD,cR,cL has the `CommShift` zero and addition fields. The descent and comparison equations concern those same structures. |
| Applies after any natural strict-tower comparison commuting with termwise shifts | Naturality of these natural isomorphisms and rho composes the displayed square with the components of any such comparison. The underlying strict morphisms are included among the localized derived morphisms, with no restriction to a selected augmentation or representative. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  Mathlib's `SheafOfModules` and its canonical abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, its localization and coherent shift.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`:
  `CategoryTheory.Abelian.functorCategoryAbelian`. The recorded evaluation
  preservation instances in `Limits.FunctorCategory.Basic`, and
  `NatTrans.mono_iff_mono_app` / `epi_iff_epi_app` in `EpiMono`, give the exact,
  levelwise strict-tower category; its record needs no repair.
- `Sheaf.CategoryTheory.StrictRoosComparison`:
  `CategoryTheory.strictRoosComparison`, its full existential signature,
  canonical coordinate constraint, fixed descent κ and rho, and every-resolution
  inclusion formula. Its existing proof returns exactly roosF, roosχ and roosEval.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosU`, `roosProj`,
  `roosι`, `roosLimitFunctor`, `roosDerivedUnit`; the model and inclusion
  coordinate constructions are used directly, not copied.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`, including
  the total-derived unit, its invertibility on K-injectives and resolution computation.
  Imported as the recorded proof input, not a second chosen derived-limit definition.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, the shift instance and `isKInjective_shift_iff`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective` and `quasiIso_iff`.
  The recorded bounded-below companion in `DerivedCategory.Plus` was also read;
  this item uses the unbounded clause only.
- Proof dependency `lem-pur-injective-tower-roos-shifts` currently has no Lean
  declaration or Mathlib match, so there is no module to import for it. Its entire
  node statement was read. It is a proof input, not a notion required to type this
  statement, so this delivery does not restate its additional Roos-triangle clauses.

Sources opened: `sites-cohomology.tex` lines 5067–5123, Tag 0941, especially the
K-injective representative with injective terms, termwise limit, and kernel SES;
`homology.tex` lines 3427–3452, Tag 011G, signed shifts and addition;
`derived.tex` lines 2471–2489, Tag 014E, signed cone and projections. The
shift-normalization refinement is the seven-step argument in the node; it is
not claimed to be verbatim in Stacks.

Edge cases checked before and after writing: r=0 gives sign 1; r=1 and r=-1 give
sign -1 and the same chain-map calculation; r+s=0 cancels signs. In characteristic
2 the negative sign equals the positive sign and all equations still type. The
zero complex, zero sheaf/ring, empty site, arbitrary negative degrees, unbounded
complexes and identity resolutions are not excluded. Positive integer towers
remain countably infinite; ℕ reindexes all positive levels, including the first.
No condition is added on the original tower transitions or on injective terms of
an arbitrary K-injective representative. Both site universes are independently
bounded by the module universe; w stays the chosen derived localization universe.

Searches actually run with the prescribed msearch wrapper:

- LeanFinder: `Normalized Roos comparison between mapping fiber and derived inverse
  limit respects integer shifts with signed first coordinate`. Eight hits, primarily
  generic `CochainComplex.mappingCone.mapHomologicalComplexXIso` variants and an
  induced-derived-functor shift instance; none states this normalized square.
- Loogle: `CochainComplex.mappingCone.shiftIso`. One hit: generic cone shift
  isomorphism, without strict towers, normalized inclusion or K-injective comparison.
- Mathlib grep: `[Rr]oos|derivedInverseLimit`. Zero hits.
- LeanSearch: `The normalized mapping cone model of derived inverse limit commutes
  with integer shifts`. Eight hits including generic cone shifts,
  `mappingCone.shiftTriangleIso`, `mappingCone.map_δ`, and exact derived-functor
  CommShift instances; none gives the named normalized Roos comparison.
- Local rg over `lean/WeilConjectures` and `lean/Sheaf` for
  `roos.*[Ss]hift|[Rr]oos.*[Ss]hift|normalized.*[Rr]oos`, and for the item id;
  read `RoosCommShift`, `RoosConeCalculus`, `StrictRoosModel`,
  `StrictRoosComparison`, `StrictRoosNormalization` and
  `StrictRoosDerivedLimitComparison`. Existing cone-shift statements cover strict
  coordinates or specialized sites, not this arbitrary-ringed-site normalized
  derived-limit square with every-resolution computation. No duplicate definition
  is introduced. `dag/lean_names_upstream.json` and both source roots contain
  neither the item id nor `normalizedRoosShiftComparison`.

The initial server compile exposed localization-universe inference metavariables.
Explicit `DerivedCategory.Q.{w}` annotations and the A parameters on the two
functors repaired the typing without restricting any universe. The next compile
succeeded but reported two line-length warnings; those lines were wrapped.

No STATEMENT-DISPUTED issue or mathematical node fault was found.

## Second reading by N9

I reread the node and the final signature together after the first compile; this
is a separate self-check, not a claim that a second agent reviewed it. The brief
forbids starting other agents; the maintainer's independent delivery review is
still required.

The small-site and commutative-ring binders match the normalized comparison
interface, exact products are explicit, both derived categories are unbounded,
and the strict tower model is reused. The coordinate equations retain the sign
only on y. The derived square has the correct order in Lean's composition
convention. κ transports the same chain shift to cD, so cD is not a free
replacement chosen to make the rho equation hold. The limit projection formula
and every-resolution equation fix cR to the specified termwise-limit shift, so
cR is also not a free choice. The inclusion is the actual roosι with zero first
coordinate. Naturality and both coherence laws are supplied by CommShift, and the
same cR is used for every resolution. No added injective-term assumption excludes
the resolution-independence clause. No statement correction was needed. The only
repairs during the rereading/compile cycle were explicit universe annotations
and line wrapping; neither changes the mathematics.

Validation: the final module compiled through `scompile.py` in sandbox and library
form with no warnings or errors (15.3 s and 15.2 s). The prescribed
`deliver2.py N9 lem-a1-normalized-roos-shift-comparison --no-push` completed with
`OK (dry run)`: commit 1346fdf05c2 passed server preflight and per-file compilation.
A final local packet comparison confirms only `lean` and the permitted added
statement dependency differ from the original node; the recorded signature is
verbatim, and the module has one theorem with one whole-body sorry and no long lines.
