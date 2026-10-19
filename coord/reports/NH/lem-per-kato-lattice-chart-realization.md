## Worker report

Repair of immutable head 913a7c2fed2f, addressing H12/H4 and H11. I inspected the
saved packet and ran the prescribed initial dry run: it passed mechanically at
0e91db7f42. The mathematical return still required the duplicate definitions to
be removed. I retained the theorem and all the accepted H3/H8 repairs, replaced
its differential interface with the landed one, and removed the duplicate files.

H12/H4: the delivery no longer contains the new node
`def-per-logarithmic-stalk-differentials` or its module
`Sheaf.AlgebraicGeometry.LogarithmicStalkDifferentials`. The item's `stmt_deps`
instead cites the existing `def-per-log-differential-stalk`, whose landed module
is `Sheaf.AlgebraicGeometry.LogDifferentialStalk`. The theorem imports that module
and uses `f.LogDifferential x` and `f.logDLog x (t j)` in `ht`. The local helper
`EtaleLogHom.globalChartStalkMap` is deleted; `hhi` uses the existing
`f.baseChartGerm x chart₀`.

H11: the former report's claim that relative logarithmic stalk differentials
were absent from the DAG was wrong. I read the existing node's full statement,
Lean record and module. Its six relation families are ordinary additivity,
ordinary Leibniz, log multiplicativity, structural compatibility, vanishing of
base ring symbols, and vanishing of base log symbols. They give precisely the
module required by this item's inline definition. The canonical base-chart map
is also already defined there. These landed declarations are used directly.

Compared with the current shared item node, only `lean` and `stmt_deps` change:
`stmt_deps` gains the existing landed `def-per-log-differential-stalk` as allowed
by brief-stage2 §5. No natural-language statement, source, proof, or other node
field is changed. No definition or dependency node is delivered. The remaining
owning-node helpers construct the actual unit subgroup and inverse-image monoid.
Only `AlgebraicGeometry.kato_lattice_chart_realization` has a postponed proof;
its source docstring retains all ten proof steps with their named inputs.

The theorem is in `Sheaf.AlgebraicGeometry.KatoLatticeChartRealization`.
Each hypothesis and conclusion is rendered below; multiplicative notation
represents the node's additive monoids and abelian groups.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Locally Noetherian fs log schemes `(X,M)` and `(Y,N)` | `X Y : FineSaturatedLogScheme.{u}`; this structure contains the locally Noetherian instance and fs log structure. |
| A morphism `f`, log smooth in the chart sense | `f : EtaleLogHom X Y` and `hf : f.IsLogSmooth`. |
| The geometric point and its ring `A` | `x : Spec (.of Ω) ⟶ X.scheme`, with `[Field Ω] [IsAlgClosed Ω]`; `strictLocalRing X.scheme x`. |
| `B = M_x^gp` | `Algebra.GrothendieckGroup (X.logStructure.toEtalePrelogStructure.stalk x)`. |
| Regard `Aˣ` as a subgroup of `B` | `f.stalkUnitSubgroup x`, the image of actual strict-local units via `unitsIn` and group completion. |
| Fixed chart `Q → N` on `Y` | `chart₀` on `Scheme.Etale.mk (𝟙 Y.scheme)` and `chart₀_isChart`. The terminal étale object represents `Y` itself. |
| `Q` fs and `Q^gp` torsion-free | `hq₀ : IsFineSaturatedMonoid q₀` and `hq₀tors : IsMulTorsionFree (Algebra.GrothendieckGroup q₀)`. |
| The prescribed `f♭` on chart germs | `f.baseChartGerm x chart₀`, explicitly `sectionMap` on the two terminal étale objects followed by the germ at `Over.homMk x`. Its group-completion extension is `Algebra.GrothendieckGroup.lift`. No homomorphism is supplied freely. |
| `r ≥ 0`, selected `t_i ∈ M_x` | `r : ℕ` and `t : Fin r → X.logStructure.toEtalePrelogStructure.stalk x`. |
| The vectors `dlog t_i` form a basis | `ht : ∃ b : Module.Basis ... (f.LogDifferential x), ∀ j, b j = f.logDLog x (t j)`. This fixes every basis vector to the chosen logarithmic symbol. |
| `n ≥ 1` invertible in `A` | `n : ℕ`, `hn : 0 < n`, `hnunit : IsUnit (n : strictLocalRing X.scheme x)`. |
| `L = ℤ^r ⊕ Q^gp` | The domain of `i` is exactly `Multiplicative (Fin r → ℤ) × Algebra.GrothendieckGroup q₀`. Finite direct sum equals product; there is no independent `L` parameter. |
| `G` finite rank free abelian | `[CommGroup G]` and `hGfree`, a finite basis of `Additive G` over `ℤ`. |
| `i : L → G` injective | `i` with that concrete domain and `hi : Function.Injective i`. |
| `G/i(L)` killed by a power of `n` | `hquot : ∃ k : ℕ, ∀ g : G, g ^ (n ^ k) ∈ i.range`. It quantifies over `G`, and does not assert that `i(L)` is torsion. |
| The given extension `h : G → B` | `h : G →* Algebra.GrothendieckGroup ...`. |
| `hi = φ`, with `φ(a,q) = Σ a_i t_i + f♭(q)` | `hhi` spells out this exact equation for every integer vector `a` and every `q : Q^gp`: the finite product of the integer powers of `of (t j)`, multiplied by the canonical lifted chart-stalk map of `q`. There is no independent `φ` parameter. |
| `h` surjects onto `B/Aˣ` | `hsurj`, surjectivity after `QuotientGroup.mk' (f.stalkUnitSubgroup x)`. |
| The prescribed inverse-image monoid `P` | `f.inverseImageMonoid x h`, the actual submonoid of `G` whose image is `of m` for some `m : M_x`. |
| `P` is fs | `IsFineSaturatedMonoid (f.inverseImageMonoid x h)`. |
| Inclusion identifies `P^gp` with `G` | `∃ e : Algebra.GrothendieckGroup P ≃* G, ∀ p, e (of p) = p.1`, parenthesized as its own conjunct. |
| The germ is `h|P` | `hP` has `∀ p, of (hP p) = h p.1`. Integrality makes this the uniquely prescribed monoid map. |
| A pointed étale neighbourhood | `W : X.scheme.Etale` and `w : (Scheme.pointSmallEtale x).fiber.obj W`. |
| A chart `P → M|W` with that germ | `hW`, `X.logStructure.IsChart W hW`, and `(germ x W w).hom.comp hW = hP`. |
| Prescribed `u(q) = i(0,q)` | `∀ q : q₀, (u q).1 = i (1, Algebra.GrothendieckGroup.of q)`. Here `1 : Multiplicative (Fin r → ℤ)` is the zero integer vector. The equality fixes every value of `u` in the actual subtype `P`, so `u` is unique; the existential supplies only its required codomain restriction. |
| Compatibility with the unchanged base chart | `f.sectionMap` from the same terminal chart on `Y` to `W`, along `W.hom ≫ f.base`, equals `hW (u q)` for every `q`. |
| The monoid-ring comparison | The pullback of `Y.logStructure.chartToSpec ... chart₀` and `Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ u))`; `MonoidAlgebra ℤ P` is the node's finite-support monoid ring. |
| This comparison map is étale | `∃ c`, its first projection is `W.hom ≫ f.base`, its second is the chart map for `hW`, and `Etale c`. The two projections characterize the canonical map uniquely. |


Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.LogDifferentialStalk`:
  `EtaleLogHom.logDifferentialRelations`, `LogDifferential`, `logDLog`, and
  `baseChartGerm`, recorded by `def-per-log-differential-stalk`. The module uses
  the actual quotient of the free module by the six relation families. Base
  relations range over all relative pointed étale objects. `baseChartGerm` is
  actual section pullback on the terminal objects followed by geometric germ.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogHom`, `EtaleLogHom.sectionMap`,
  `EtalePrelogStructure.stalk`, `EtalePrelogStructure.germ`,
  `EtaleLogStructure.unitsIn`, and `EtaleLogStructure.IsChart`.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`:
  `EtaleLogHom.IsLogSmooth` and `EtaleLogStructure.chartToSpec`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`:
  `pointedEtaleStalk`, `pointedEtaleGerm`, and the pointed-neighbourhood diagram.
- Mathlib `AlgebraicGeometry.Etale`, `CategoryTheory.Limits.pullback`,
  `pullback.fst`, `pullback.snd`, `Algebra.GrothendieckGroup.of` and
  `Algebra.GrothendieckGroup.lift`.

The proof imports from the accepted packet are retained: chart spreading,
`face_sharpening`, `Submodule.basisOfPid`, finite commutative monoid
presentations, `ΓSpec.adjunction`, local finite presentation, and the upstream
small-étale representable sheaf module. The ten-step docstring also names the
not-yet-stated infinitesimal calculus, integral-chart thickening, and ordinary
unique-lifting criterion by their DAG IDs.

Edge cases checked:

- `r = 0`: `Fin 0 → ℤ` is the zero free factor, the product in `hhi` is `1`,
  and `ht` requires the differential module to have the empty basis.
- Trivial `Q`: the base summand and its contribution to `hhi` disappear.
- `n = 1`: `hquot` says every `g` is in `i.range`, exactly the zero quotient.
  It does not force `G` or `L` trivial. For any positive `n`, taking `G = L`
  and `i = id` meets the corrected quotient condition, including nonzero `L`.
- For a nontrivial quotient, the rank-one lattice inclusion by an integer `d`
  has the required quotient condition when `d` divides `n^k`; its image is not
  required to be torsion. This tests the quotient condition independently of the free lattice.
- A chosen `t_j = 1` has zero `logDLog`, hence cannot be a basis vector in a
  nonzero differential module; `ht` detects this instead of ignoring `t`.
- The invertibility of `n` excludes the bad characteristic in the Kummer case.
- Empty schemes remain allowed as fs log schemes; specifying `x` already selects
  the nonempty pointed case, just as the node does.
- `u` cannot be altered while keeping the new pointwise equation: subtype
  extensionality fixes it. The comparison is likewise fixed by its projections.


Searches from the prior packet, retained as search history (not as evidence of
absence from the current DAG): `msearch.py ... leanfinder` on relative logarithmic
differentials and prescribed log-smooth charts found no matching log-scheme
statement; `... loogle` on group completions and logarithmic differentials found
no match; `... grep` on `LogDifferential|logDifferential|LogScheme|LogStructure`
and `rg` in the named upstream, Mathlib and project trees were also used. The
old conclusion that no DAG node carried the differential notion is withdrawn.
The repair's positive match is `def-per-log-differential-stalk` and its recorded
`Sheaf.AlgebraicGeometry.LogDifferentialStalk`, whose source was opened in full.

Previous theorem-specific searches: `msearch.py ... leanfinder` on
"Prescribed lattice logarithmic chart realization log smooth morphism basis dlog"
returned eight unrelated number-field logarithmic-lattice results;
`... loogle` on `Algebra.GrothendieckGroup.lift, MonoidHom.codRestrict` returned
no hits; `... grep` on
`kato_lattice_chart_realization|logarithmic.*chart|chartStalkMap` in
AlgebraicGeometry returned no hits. Direct `rg` of the item ID in upstream and
of `kato_lattice_chart_realization|globalChartStalkMap` in the project found no
existing theorem. Those searches do not override the landed differential match.

The original packet read the source with `pdftotext`: ILO XVI Proposition 3.6.3,
printed p.252, has the fixed chart on `Y`, selected `dlog t_i` basis,
n-primary lattice quotient, and prescribed inverse-image monoid. The returned
review accepted this statement and its ten-step docstring; this repair changes
only the interfaces used for two of its notions. No statement dispute remains.

Validation: `scompile.py NH lem-per-kato-lattice-chart-realization
lean/Sheaf/AlgebraicGeometry/KatoLatticeChartRealization.lean` compiled the sole
delivered file cleanly (sandbox 3.7 s, library 4.0 s). The final dry run repeats
per-file compilation and server preflight.

## Second reading by NH

I reopened the item node, repaired module, landed differential node and landed
module. This is the dispatcher's required worker self-check; the maintainer
supplies the independent review. No sub-agents were started.

For H12/H4, I checked that the deleted new node/module are absent from the
packet, the item cites `def-per-log-differential-stalk`, and the import is
`Sheaf.AlgebraicGeometry.LogDifferentialStalk`. `ht` uses the actual quotient
`f.LogDifferential x`, with every basis vector equal to the selected
`f.logDLog x (t j)`. I compared all six relation families with the node's inline
definition. `hhi` uses the landed `baseChartGerm`, whose definition is the same
terminal-object section pullback and germ as the removed helper. There is no
local declaration of `globalChartStalkMap` or of any differential notion.

For H11, the report now positively identifies the existing DAG node and module
and withdraws its former false absence claim. I read the dependency signatures
and source docstrings, including the actual quotient and base chart map.

The table above was checked against the actual theorem binders and conclusion.
The accepted H3 fixes remain: `L` is the concrete product of the integer lattice
and `Q^gp`; `hhi` fixes its image using `t` and the base chart; `hquot` quantifies
over `G` and expresses annihilation of the quotient; `u(q)=i(0,q)` is fixed
pointwise. The `P^gp ≃ G` conjunct ends before the later existential witnesses.
The actual inverse-image monoid, its specified germ, the pointed neighbourhood,
the unchanged base chart and both projections of the étale comparison remain
exactly as in the accepted statement. The ten proof paragraphs are unchanged.
I revisited `r=0`, `n=1`, trivial `Q`, and the identity lattice inclusion; all
still express the required cases after replacing the differential interface.
The sole theorem has `sorry`; both remaining helpers have real data, all
variables/universes are explicit, and `lean.statement` is extracted verbatim.
