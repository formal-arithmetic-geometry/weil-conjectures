## Worker report

The module `Sheaf.AlgebraicGeometry.RaynaudGenericAmplePowerModel` states
`AlgebraicGeometry.raynaud_generic_ample_power_model`, with its sole proof `sorry`.
No construction or theorem is proved, and no definition is added. The natural-language
proof in the docstring is the node's two-step specialization of generic symmetrization,
followed by the tensor calculation giving exponent `2*a_i`.

Hypotheses, clause by clause:

- `T : Scheme.{u}` is the base scheme; `[IsAffine T]` is its affineness.
- `[IsIntegral T]` includes nonemptiness and integrality. `[IsLocallyNoetherian T]`
  together with affineness is exactly Noetherianity; affineness already gives
  quasi-compactness. It neither excludes nor admits an additional base case.
- `hT` says that each local ring `T.presheaf.stalk t` is a domain and integrally
  closed, exactly the stipulated normality.
- `H : Grp (Over T)` contains the actual structure map `H.X.hom`, multiplication,
  identity and inverse, satisfying the group axioms. `[IsCommMonObj H.X]` imposes
  commutativity of that multiplication.
- `[Smooth H.X.hom]` and `[IsSeparated H.X.hom]` are smoothness and separatedness;
  the latter says exactly that the diagonal is a closed immersion.
- `[LocallyOfFinitePresentation H.X.hom]` and `[QuasiCompact H.X.hom]` express
  finite presentation: separatedness already implies quasi-separatedness.
- `hH : HasSemiabelianGeometricFibres H` is the existing exact fppf extension
  predicate. Its geometric points quantify over algebraically closed fields, its
  rank is any natural number (including zero), its kernel is the existing split
  torus, and its quotient is a proper smooth connected abelian variety. It uses
  the given group laws. The definition and the abelian-variety definition were read.
- `T.fromSpecResidueField (genericPoint T)` is the canonical generic-point map,
  and `(Over.pullback ...).mapGrp.obj H` is the generic fibre with its induced law.
  The `IsProper` instance on its structure map is precisely generic properness.
- `M` belongs to the modules on that very generic fibre. `[M.IsInvertible]` and
  `hM : Scheme.Modules.IsAmple _ M` impose invertibility and absolute ampleness.
- `symmetry` is an actual isomorphism from the tensor inverse-image of `M` along
  the generic group's inverse `ι[...]` to `M`. No choice of an unrelated inverse
  map or an abstract pullback functor is made.

Conclusions, clause by clause:

- `∃ (I : Type u) (W : I → T.Opens), (⨆ i, W i) = ⊤` gives a covering of the base.
  `IsAffineOpen (W i)` makes each covering member affine. The covering may be
  chosen without empty members; `Nonempty (W i)` records that harmless choice.
- `∃ d : ℕ, 1 ≤ d` gives exactly each member's positive exponent.
- `N : (pullback H.X.hom (W i).ι).Modules` and `N.IsInvertible` give the ordinary
  invertible module on `H_{T_i}`. There is no line supplied on the total group.
- The `Nonempty (... ≅ ...)` gives an isomorphism between the restrictions of `N`
  and `M.tensorPow d` to
  `H_{T_i} ×_H H_eta`. The two arrows are its actual `pullback.fst` and
  `pullback.snd`, and both module restrictions use `tensorPullback`. Because `T`
  is integral and `W i` is nonempty, `eta` lies in `W i`. Consequently the second
  projection is canonically an isomorphism to all of `H_eta`. Thus this clause is
  exactly `N_i|_{H_eta} ≅ M^{tensor d_i}`, written on its canonical base-change
  model; it is not agreement just on a smaller generic open or an arbitrary map.
- For every `V : (W i).toScheme.Opens` with `IsAffineOpen V`, the last clause
  requires ampleness of the actual tensor pullback of `N` to the inverse-image
  open under `pullback.snd H.X.hom (W i).ι`. This is precisely relative ampleness
  above every affine base open. The existential invertibility proof `h` supplies
  the proof argument of the existing `IsAmple` definition, and imposes no
  additional mathematical condition on an invertible line's restriction.
- No cubical structure, rigidification, supplied total-group line, or extension
  of `M` itself is asserted.

Dependency declarations used (their full signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain` on every stalk, as the normal-ring record prescribes.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  `IsSeparated` is its imported diagonal predicate.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (publicly imported by
  Ample): `Scheme.Modules.IsInvertible`, `Scheme.Modules.tensorPow`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the publicly
  imported `Scheme.Modules.tensorPullback`, retaining its actual inverse-image,
  change-of-rings and sheafification construction. The adjunction itself is not
  needed in the theorem signature.
- `Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres`:
  `AlgebraicGeometry.HasSemiabelianGeometricFibres`. Its existing landed node
  `def-sfb-semiabelian-geometric-fibres` is added to `stmt_deps`, as permitted for
  landed notions. No new node or dependency replacement is needed.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.fromSpecResidueField`;
  `CategoryTheory.Over.pullback`, `Functor.mapGrp`, and `Limits.pullback` give
  the canonical base changes, rather than separately invented fibre data.

The proof dependency `lem-sfb-raynaud-generic-ample-symmetrization` currently has
no Lean record or module to import. Its proof plan is preserved in the docstring;
no import for an unstated theorem is invented. No statement or proof fields change.
The item is an auxiliary node, not the blueprint unit's own statement. The newest
blueprint `sk-thm-sf-ctf-stability/_section.md` was read; this delivery changes none
of its targets or routes. The node explicitly records its original Raynaud source
as WANTED and its precise formulation as agent responsibility, which the module
also records without pretending the missing original was read.

Edge cases checked before writing: the empty base is excluded by the original
integrality assumption, and an empty covering cannot cover this base. Empty cover
members can always be discarded. Rank zero, a trivial group, a field base, exponent
one, and characteristic two are all admitted. The doubling in the proof is integer
exponent arithmetic, so characteristic two creates no exception. A nonempty open
of an integral base contains its generic point, so the generic comparison covers
its entire fibre. `u` is explicit; geometric fields and schemes use the same
universe as the existing semiabelian predicate, and no equality of independently
specified universes is introduced.

Searches for an existing declaration:

- `msearch.py ... leanfinder` query: "An ample symmetric line bundle on the
  generic fibre of a semiabelian scheme extends locally after a positive tensor
  power to a relatively ample line bundle". Eight hits on affine section
  localization, affine-space maps, affine-limit sections and affine-local ring
  properties; none states this result.
- `msearch.py ... leansearch` query: "An ample symmetric invertible sheaf on the
  proper generic fibre of a semiabelian group over a normal noetherian base has
  locally a relatively ample extension after a positive tensor power". Eight
  hits on relative Picard groups of rings, tensor products of invertible ordinary
  modules, sheaf cohomology and abelian module categories; none is this result.
- `msearch.py ... loogle '"IsAmple", "IsInvertible"'`: zero hits.
- `msearch.py ... grep 'Raynaud|semiabelian|semiAbelian|RelativelyAmple'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for Raynaud, semiabelian,
  generic ample powers and relative ampleness found the existing semiabelian
  predicate, symmetric-line prolongation, local ample-line existence, and ample
  definitions, but no theorem of this signature. The two existence results
  differ: prolongation assumes no ampleness and imposes overlap comparison with
  a dense-open line; local ample-line existence specifies no generic line.
- `rg -n 'lem-sfb-raynaud-generic-ample-power-model' lean/WeilConjectures`
  returned no hits. The dependency node records were read directly, including
  the field/list form of Mathlib matches where applicable.

Validation: `scompile.py Q145 lem-sfb-raynaud-generic-ample-power-model <file>`
succeeded on both the sandbox probe and actual library module, about three seconds
per compile, with no errors or non-sorry warnings. Every variable and universe is
explicitly bound; both automatic-implicit options are disabled.

No STATEMENT-DISPUTED issue, node correction, new definition, or dependency-module
repair is needed.

## Second reading by Q145

The dispatcher forbids starting other agents, and the maintainer independently
reviews this delivery. This section records this worker's second reading, not a
claim of an independent sub-agent review. I reopened the node and module and
checked each binder and conclusion against the mapping above. In particular I
checked that affineness plus local Noetherianity gives the full Noetherian base,
that quasi-compactness belongs to finite presentation rather than an extra
assumption, that generic properness and symmetry are retained despite being
unneeded by the first proof step, and that the final quantifier is over every
affine open, not just the covering member. I checked the types of both projections
in the generic comparison: the first targets `H_{T_i}`, and the second targets
`H_eta`; their source is the same pullback, canonically `H_eta` by nonemptiness
of the base open. I checked that no rigidification or cubical structure appears.
No mismatch was found and no statement change was made.
