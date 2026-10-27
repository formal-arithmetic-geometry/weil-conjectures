## Worker report

Stage 2, Q11, 2026-10-22. The delivery states the reviewed node
`lem-trf-relative-cohen-flat-presentation` in
`Sheaf.RingTheory.RelativeCohenFlatPresentation`, declaration
`IsLocalRing.exists_relative_cohen_flat_presentation`. Its only theorem has proof `sorry`.
The auxiliary definition `MvPowerSeries.coefficientExtensionInl` is a real composite of
Mathlib's coefficient map and variable renaming, not a choice or a postponed construction.
It belongs to the item's power-series diagram and is listed in `lean.declarations`.

The old dispatcher failure concerned resplitting stage 1. The live node is already split
and reviewed by N5, but has no `lean` record. This delivery preserves that split, its
review, statement and every dependency and adds only `lean`.

Hypotheses and clauses, in the order of the node:

- Nonzero commutative Noetherian local Q-algebras A and B: `CommRing`, `IsNoetherianRing`,
  `IsLocalRing`, and `Algebra ℚ` for both types. `IsLocalRing` includes nontriviality.
  The independent universes `u` and `v` allow arbitrary-sized A and B.
- The ring map f is `algebraMap A B` for `[Algebra A B]`, with
  `[IsLocalHom (algebraMap A B)]` and `hflat : (algebraMap A B).Flat`.
  This is the project's convention for a ring map when residue fields are involved.
  Every ring map can be encoded by its `toAlgebra`; rational algebra structures are unique,
  so no extra rational-linearity or scalar-tower hypothesis is imposed.
- K and L are exactly `IsLocalRing.ResidueField A` and `IsLocalRing.ResidueField B`.
  The inclusion K to L is `IsLocalRing.ResidueField.map (algebraMap A B)`.
- The closed fibre is exactly `B ⧸ (maximalIdeal A).map (algebraMap A B)`.
  `IsRegularLocalRing` and `hdim` give regular locality and dimension `s : ℕ`.
- A-hat and B-hat are `AdicCompletion (maximalIdeal A) A` and its B analogue.
  The existential ring map `h` is characterized on EVERY d-th quotient: if the d-th
  component of z is x mod m^d, the d-th component of h(z) is f(x) mod n^d.
  Quotient surjectivity means this fixes each component of h(z), hence uniquely specifies
  the induced completion map. This is not an unconstrained additional map or assumption.
- The existential ring maps `a` and `b` land in the corresponding completions.
  Their `evalOneₐ` identities make them sections of the original residue maps, since
  `ResidueField A` is definitionally A/m. Field-to-nonzero-ring maps are injective.
- `b.comp (ResidueField.map (algebraMap A B)) = h.comp a` is precisely b restricted to K.
- `e : ℕ` permits zero base variables. The ideal `I` is an ideal of K[[Fin e]];
  its inequality against the span of the variables is exactly I contained in (X).
- `α : (K[[Fin e]] / I) ≃+* A-hat` is the first displayed isomorphism, in the
  inverse orientation; `β` is the second, from L[[Fin e ⊕ Fin s]] / IS to B-hat.
  Here IS is `I.map (MvPowerSeries.coefficientExtensionInl ... e s)`.
- The helper is literally `rename Sum.inl` after `MvPowerSeries.map` of the induced
  residue-field map. It extends K to L and retains precisely the X variables.
- The formulas for α and β on quotient constants give respectively a and b.
  A ring equivalence fixing these scalar maps is exactly a K- or L-algebra equivalence.
  The section identities ensure identity on residue fields. No arbitrary coefficient
  automorphism is allowed.
- The formula for every `F : MvPowerSeries (Fin e) (ResidueField A)` is the commuting
  power-series presentation square: β(j(F) mod IS) = h(α(F mod I)). This says exactly
  that the isomorphisms identify h with coefficient extension and X inclusion.
- A ring isomorphism of local rings identifies units, hence maximal ideals and all powers;
  consequently these are isomorphisms of complete local algebras, with no topology omitted.
- The last two conjuncts express the regular system of parameters explicitly as the node
  defines it. The classes of `β(X (Sum.inr j) mod IS)` generate the image of B-hat's
  maximal ideal in B-hat/m B-hat, and that quotient has Krull dimension s. The ideal
  m B-hat is written as the image of m under A to A-hat to B-hat; this is the same
  ideal as extending m A-hat along h. The image of the maximal ideal is the maximal
  ideal of this local quotient, so no quotient-instance choices enter the statement.
- There is no finite-type, finite-presentation, finite residue extension, chosen parameter
  hypothesis, or finite-dimensional field-extension hypothesis anywhere in the signature.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the abbreviation
  `IsNoetherian R R`, equivalent to every ideal being finitely generated.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, flatness of the target module for
  the map's algebra structure.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: the recorded dependency module is publicly
  imported. This item uses its dependency node's ring clause, Mathlib's
  `IsRegularLocalRing` from `Mathlib.RingTheory.RegularLocalRing.Defs`, not the scheme
  predicate `AlgebraicGeometry.IsRegularScheme`. Its `mathlib_match` explicitly supplies
  the ring clause, including Noetherianity and locality.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, with values in
  `WithBot ℕ∞`. Finite dimensions are cast from ℕ.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `AdicCompletion.evalₐ` and `AdicCompletion.evalOneₐ`; `.LocalRing` supplies locality
  of Noetherian local completions.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `C`, `X`, `map`;
  `.Rename` supplies `MvPowerSeries.rename`. Fin e gives precisely finitely many variables.
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: `ResidueField`, its quotient
  interpretation, and `ResidueField.map` for a local homomorphism.

The modules of all recorded proof dependencies are imported with plain `import`.
The mathematical proof is copied in full, in eight numbered steps with named DAG uses,
into the theorem docstring. The unrecorded proof dependency
`lem-trf-regular-complete-coefficient-coordinates` has no Lean declaration yet and therefore
no module to import; it is a proof dependency only and is not needed to type this statement.
The other proof leaves without Lean records are supplied by their recorded Mathlib matches:
completion locality/completeness, quotient locality, surjective Noetherian images, and
characteristic-zero formal smoothness. No missing statement notion or dependency repair
is required, and no new DAG node is added.

Source reading: Stacks more-algebra.tex, Tag 07NQ (label
`proposition-fs-flat-fibre-fs`), especially the special-fibre isomorphism and kernel/Nakayama
argument at lines 10100–10155; algebra.tex, Tag 032A (Cohen coefficient section and quotient
presentation), and Tag 0C0S(2), including its proof at lines 45036–45066. The node is explicitly
a coefficient-compatible refinement, not a claim that 07NQ verbatim states this theorem.
The compatibility proof in step 3 uses formal smoothness of arbitrary characteristic-zero
field extensions, so no finite-type assumption on K to L was introduced.

Edge cases checked before and after writing:

- A and B fields, arbitrary extension L/K: e=s=0 and I=0. Both power-series rings reduce
  to the coefficient fields; the parameter span and the maximal ideal of the closed fibre
  are zero. Thus the theorem includes transcendental and arbitrarily large field extensions.
- The identity A=B, including singular A: s=0, no T variables, and the same relation ideal
  after coefficient extension. No accidental regularity of A is assumed.
- A=Q and B=Q[[T_1,...,T_s]]: e=0, I=0, and the whole target presentation is relative.
- A=Q[ε]/(ε²), B=A[[T]]: e=1, I=(X²), s=1. This checks that the relation ideal is
  extended as an ideal, rather than incorrectly removed or assumed zero.
- At d=0 the completion-characterization implication is harmless; positive d determine
  every component. It does not add an injectivity assumption on f or its completion.
- The zero ring is excluded by the node's nonzero local-ring hypotheses. `s=0` and `e=0`
  are both permitted; no empty-family case is lost.

Searches actually run (msearch.py, Q11/item; searches.jsonl retains the exact records):

- LeanFinder: “A flat local homomorphism of Noetherian rational algebras with regular
  closed fiber has compatible coefficient fields and power series presentations after
  completion”. Eight hits concern smoothness/standard smoothness and flatness; no
  coefficient-compatible Cohen presentation.
- Loogle: `MvPowerSeries, AdicCompletion, RingHom.Flat`. Zero hits.
- Mathlib grep: `relative.*[Cc]ohen|coefficientField|coefficient_field`, RingTheory.
  Zero hits.
- LeanSearch: “Compatible coefficient fields and a relative Cohen power series
  presentation for a flat local map with regular closed fibre in characteristic zero”.
  Eight hits concern presentation coefficients, flat locality and univariate local rings;
  none provides either completed relative presentation.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for relative Cohen names and the item
  id finds only unrelated relative Cohen–Macaulay material and the existing
  SmoothLocalTangentConeExtension proof docstring which cites this still-unstated node.
- Exact-name search of Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json for
  `coefficientExtensionInl|exists_relative_cohen_flat_presentation` finds no declaration.

No statement correction, disputed statement or hollow definition is present.

## Second reading by Q11

The dispatcher explicitly forbids starting another agent, so this is a separate final
self-check of the node and final source, not a claim of an independent worker's reading.
The maintainer performs the independent review of this delivery.

I reread the TeX node against the signature clause by clause. Flat local Q-algebras are
represented by the two ring structures, local/Noetherian instances, rational algebra
structures, algebraMap and its flat/local properties. The original closed fibre, regularity
and dimension s are unchanged. K and L are the original residue fields, not arbitrarily
chosen isomorphic fields. The every-quotient condition specifies the canonical completed
map and both evalOne identities refer to the original residue fields. The equation between
sections uses the induced K to L map. The ideal and two quotient ring equivalences are on
exactly K[[X]] and L[[X,T]], with the extension of the same ideal. The two constant formulas
prevent the nontrivial residue automorphism defect discussed in the stage-1 review. The
all-series formula supplies the full map compatibility, beyond checking variables alone.
The last span equation and dimension equation include every clause in the node's own
explicit definition of a regular system of parameters. Both zero-variable cases and
non-finite-type field extensions remain included. No statement mismatch was found.

The first compiler attempt exposed two guessed proof-module paths that do not exist;
I reread the actual proof-dependency records, removed those imports, and retained the
Mathlib completion-locality/completeness interface actually recorded for those leaves.

Validation: the prescribed `scompile.py Q11 lem-trf-relative-cohen-flat-presentation`
compiled the final file cleanly in sandbox mode (15.0 seconds) and its actual library
module mode (9.3 seconds), exit 0 and no warnings. Every universe and variable is explicit,
with `autoImplicit false`. No global build or direct live-repository mutation was run.
