## Worker report

The saved module `Sheaf.AlgebraicGeometry.PuncturedPerverseHighComparison` states
`AlgebraicGeometry.Etale.isIso_punctured_perverse_high_comparison`. It has one theorem,
with `sorry`, and no new definitions. I retained the earlier packet after checking it
against the current node and compiling it with the prescribed wrapper. The initial
required dry run failed solely because this report was missing.

Source read: ILO, Travaux de Gabber, Expose XVII, Lemma 5.3.2, printed pp. 288–289,
including the cone argument and the reference to Proposition 3.2.1. Its punctured
strictly henselian excellent normal local scheme, perverse upper bound, zeroth
truncation, and degree range agree with the node. The node spells out the stalk bound
and specializes the coefficient ring to Z/ell^n. No statement correction is needed.

Hypotheses and clauses, matched individually:

| Node | Lean |
| --- | --- |
| ell prime | `ell : ℕ`, `_hell : Nat.Prime ell` |
| n at least 1 | `n : ℕ`, `_hn : 1 ≤ n` |
| Lambda = Z/ell^n | `ULift.{u + 1} (ZMod (ell ^ n))` throughout |
| Noetherian local scheme X | `R : Type u`, `[CommRing R]`, `[IsNoetherianRing R]`, and `e : X ≅ Spec (.of R)` |
| strictly henselian | `[IsStrictlyHenselianLocalRing R]`, which extends the existing henselian local ring class and supplies separably closed residue field |
| excellent | `_hexc : IsExcellent R` |
| normal | `_hnormal : ∀ (p : Ideal R) [p.IsPrime], IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)` |
| dimension d at least 2 | `d : ℕ`, `_hd : 2 ≤ d`, `_hdim : ringKrullDim R = (d : WithBot ℕ∞)` |
| ell invertible on X | `_hellunit : IsUnit (ell : R)` |
| x is the closed point | `x : X`, `_hx : e.hom x = IsLocalRing.closedPoint R` |
| U = X minus x | `U : X.Opens`, `_hU : (U : Set X) = {x}ᶜ` |
| M in D+(U_et,Lambda) | `M : DerivedCategory.Plus (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))))` |
| every geometric point above y | `_hM` quantifies over `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.toScheme)`; its image in X is `U.ι (s default)` |
| phi(y) = max(0,2 dim O_X,y - 2) | `((2 * ENat.toNat (WithBot.unbotD 0 (ringKrullDim (X.presheaf.stalk (U.ι (s default))))) - 2 : ℕ) : ℤ)` |
| H^a(M restricted to the geometric point) vanishes for a > phi(y) | `_hM` concludes `IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj ((DerivedCategory.homologyFunctor _ a).obj M.obj))` under that strict inequality |
| specified alpha : Lambda_U isomorphic to ordinary tau_le_0 M | `alpha : constantComplex ... U.toScheme ≅ (DerivedCategory.TStructure.t.truncLE 0).obj M.obj` |
| u is alpha followed by ordinary truncation | `alpha.hom ≫ (DerivedCategory.TStructure.t.truncLEι 0).app M.obj` |
| every q at least 2d | `q : ℤ`, `_hq : 2 * (d : ℤ) ≤ q` |
| displayed H^(q-1)(u) is an isomorphism | `IsIso ((cohomology (ModuleCat.{u + 1} ...) U.toScheme (q - 1)).map (...))` |
| hypercohomology by derived global sections | existing `AlgebraicGeometry.Etale.cohomology`, defined as `rightDerivedGlobalSections A X ⋙ DerivedCategory.homologyFunctor A i` |

The affine presentation adds no geometric assumption: a local scheme is the spectrum
of its local ring. The chosen isomorphism also locates its closed point without choosing
an arbitrary point. ULift is the standard coefficient size transport, retaining every
finite coefficient module. All universes are bound explicitly and `autoImplicit` is
false. The geometric field universe is the scheme universe, as in the recorded
geometric-point interface; it is not an independent smaller universe. The stalk
condition on cohomology sheaves is equivalent to cohomology of the restricted complex
because geometric stalks are exact. Module-valued derived sections retain the natural
coefficient action; their isomorphisms are equivalently isomorphisms of the underlying
abelian groups.

Statement dependency declarations used, with source signatures/docstrings inspected:

- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`; its definition
  is `IsQuasiExcellent R ∧ IsUniversallyCatenary R`. Both include the stated Noetherian,
  finite-type-algebra and chain conditions.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, with `IsDomain` and `Localization.AtPrime`, using the prescribed
  inline normal-ring condition.
- `def-weil-pbc-henselian-terminology`:
  `WeilConjectures.Mathlib.RingTheory.Henselian`, `IsStrictlyHenselianLocalRing`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim : WithBot ℕ∞`, the dimension of the prime spectrum.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  the existing `DerivedCategory.Plus` / `DerivedCategory.homologyFunctor` encoding on
  `Sheaf ... (ModuleCat ...)`. Its current source was read with `scompile.py --source`
  because it is absent from the older local checkout.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`,
  and the inline `Spec Ω ⟶ U` encoding; `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` identifies this with a point and a residue
  field embedding. The geometric stalk is `Scheme.pointSmallEtale s` followed by
  `sheafFiber` from `Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `def-weil-pbc-etale-cohomology`:
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` and `.cohomology`.
  `constantComplex` is the existing coefficient object from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, imported through the
  recorded derived-category module.

The proof docstring retains all six DAG proof steps, including finite ell-power
coefficient devissage, the pointwise support bound, finite Postnikov induction and the
final long exact sequence with both outer terms zero. Private proof imports retain
Mathlib's scheme-stalk dimension formula, stalk exactness, short-exact triangle and
homology sequence; upstream stalk conservativity, derived triangulated functor and
truncation triangle; and the recorded enough-injectives and truncation modules.
`lem-per-punctured-support-cohomological-bound` currently has no Lean record and is a
proof prerequisite only, so there is no module of that node to import. No missing
statement notion is being replaced by an assumption.

Edge cases checked: `n = 1` is included; `n = 0` is excluded by the node itself. At
local height 0 or 1 the natural subtraction in phi gives 0, not a negative bound; at
height 2 it gives 2. Finite dimension of X makes every local-ring dimension finite,
so `unbotD`/`toNat` does not lose information. At `d = 2`, positive cohomology of the
cone vanishes everywhere and the proof filtration has no induction indices. The
boundary `q = 2d` is included: the two outside groups have degrees `2d-2` and `2d-1`.
The prime may be any prime, including 2. Mixed characteristic and equal characteristic
are both allowed when ell is a unit. No constructibility or finite-type-over-a-field
hypothesis was added. `M = Lambda_U` with its zeroth-truncation isomorphism recovers
an isomorphism. An empty scheme or zero ring is incompatible with the specified
strictly local scheme of dimension at least 2, as in the node.

Searches retained from the saved `searches.jsonl`:

- LeanFinder, 2026-10-18: "High degree etale hypercohomology comparison on a punctured
  strictly henselian normal excellent local scheme for a complex with perverse stalk
  bounds and constant zeroth truncation". Eight hits, including scheme etale topology,
  etale loci and ordinary complex lifting results; no comparison theorem.
- Loogle: `"perverse"`; zero hits, repeated in the earlier attempt.
- Mathlib grep: `perverse|punctured.*[Cc]ohom|[Cc]ohom.*punctured`; zero hits.
- LeanSearch: "Etale hypercohomology comparison on a punctured strictly henselian local
  scheme from a constant zeroth truncation and pointwise stalk dimension bound".
  Eight hits on stupid truncation and etale schemes/sites, no matching theorem.
- Current `rg` of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`,
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf` and `dag/lean_names_upstream.json`
  for the item id, `isIso_punctured_perverse_high_comparison`, and
  `perverse.*high|high.*perverse`: no duplicate.

Validation: `scompile.py Q06 lem-per-punctured-perverse-high-comparison <module>`
compiled both sandbox and library module cleanly (2.8 s and 2.7 s). The saved node
copy differs from the current repository only in `lean`; its signature is verbatim
from the module. No new nodes, dependency repairs, statement corrections or disputed
statements are in this packet.

## Second reading by Q06

This is the dispatched worker's second pass, not an independent-worker review: the
current human brief forbids starting other agents and assigns independent delivery
review to the maintainer. I reopened the node and the saved Lean module after the
first clean compile and checked every row of the mapping above.

The input ring has the exact four local hypotheses: Noetherian, excellent, normal,
and strictly henselian. The spectrum presentation, dimension equality and closed-point
condition preserve the scheme in the node. The open is its complement. The coefficient
ring is precisely the lifted prime-power quotient, not a field replacement. The test
point lands on U and the bound measures its local ring in X. The natural subtraction
implements the maximum with zero. The specified alpha and truncation inclusion occur
in the arrow passed to cohomology, so no arbitrary comparison morphism was introduced.
The integer degree uses `q - 1` and includes the boundary `q = 2d`. The output uses the
recorded derived-global-sections functor and asks that this exact map be an isomorphism.
I found no signature mismatch and retained the saved statement unchanged. I supplied
the missing worker report; no proof or new definition was added.
