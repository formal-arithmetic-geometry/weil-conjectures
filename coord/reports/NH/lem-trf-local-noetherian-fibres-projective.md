## Worker report

The new module `Sheaf.RingTheory.NoetherianGeometricallyIntegralProjective` states
`Algebra.projective_of_noetherian_geometricallyIntegral_fibres`, with proof `sorry`.
It states the Noetherian finite-type theorem in Stacks Project, More on Flatness,
`lemma-fibres-irreducible-flat-projective`, Tag 05FS. Its docstring gives all ten
steps of the node's proof, including the domain-localization preparation for generic
freeness, the identification of the associated primes of a fibre, and the properness
argument using a maximal ideal of the completed base.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative rings `R` and `S`: `(R : Type u) (S : Type v) [CommRing R]
  [CommRing S]`, with independent explicitly bound universes.
- The unital homomorphism `R → S`: `[Algebra R S]`, with `algebraMap R S` the
  specified homomorphism. An arbitrary homomorphism has exactly this algebra
  structure through `RingHom.toAlgebra`; no injectivity or other property is added.
- Noetherian `R`: `[IsNoetherianRing R]`.
- Finite type: `hfinite : RingHom.FiniteType (algebraMap R S)`.
- Flat: `hflat : RingHom.Flat (algebraMap R S)`.
- Every prime of `R`: `∀ p : PrimeSpectrum R` in `hfibres`.
- Its fibre algebra: Mathlib's `p.asIdeal.Fiber S`, definitionally
  `κ(p) ⊗[R] S`. Tensor symmetry identifies this canonically with the node's
  `S ⊗[R] κ(p)`, as an algebra over `κ(p)`.
- Geometrically integral over the residue field: `GeometricallyIntegral` applied
  to `Spec.map` of the canonical field-to-fibre ring map. This is exactly the
  recorded scheme definition: every field extension of the residue field has
  integral affine spectrum, equivalently its algebra is a nonzero domain.
- Conclusion: `Module.Projective R S`, with the module structure of the same
  `R`-algebra. No finite generation as an `R`-module is asserted or assumed.

The map in the fibre clause is
`(algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)).ulift.{max u v, max u v}`.
This is the functorial lift of the actual canonical structure map, defined by
conjugating with `ULift.ringEquiv` on source and target, not an arbitrary map or
an additional assumption. The lift places both rings in `Type (max u v)`, so the
spectrum map can be taken in one category of schemes while `R` and `S` keep
independent universes. The two lifted rings and this map are canonically
isomorphic to the original rings and map. This preserves the base-change
condition, including the identity extension. The standard scheme definition
quantifies over extension fields in that common universe; as usual for affine
geometric integrality, arbitrary extensions reduce to the subfields generated
by finitely many coefficients of any proposed zero-divisor relation. Thus it
excludes no field-extension case of the source.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, definitionally
  Noetherian as a module over itself, equivalently every ideal is finitely generated.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, and
  `RingHom.flat_algebraMap_iff` identifying it with `Module.Flat R S`.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`, the canonical free
  module surjection splitting, with the lifting/direct-summand interpretation.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`; `Spec.residueFieldIso` canonically identifies the
  recorded scheme residue field at `p` with the ring-theoretic
  `p.asIdeal.ResidueField` used by `Ideal.Fiber`. Its compatibility lemma
  `Spec.algebraMap_residueFieldIso_inv` identifies the structure map too.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`,
  defined by `geometrically IsIntegral`; the full signature and docstring were
  read together with `geometrically_iff_of_commRing` in `Geometrically.Basic`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`; its definition uses
  `Algebra.FiniteType` with precisely the ring map's induced algebra structure.

All recorded modules of the stated proof dependencies are imported as proof
imports. This includes the generic-freeness, completion, complete-base criterion,
nilpotent-lifting, and faithfully flat descent modules, together with the named
Mathlib completion, localization, and minimal-prime inputs. There is no new
mathematical definition or postponed helper theorem.

Edge cases checked:

- If `R` is the zero ring, it has no prime ideals. The fibre clause is vacuous,
  but an algebra over `R` is also the zero ring, hence projective, as required.
- If `S` is the zero ring and `R` has a prime ideal, the corresponding fibre is
  the zero ring. Its spectrum is empty and not integral, so the hypothesis fails.
  Empty fibres are not silently allowed.
- For the identity algebra `S = R`, every fibre is the residue field, including
  its identity extension; the conclusion is the free rank-one module case.
- A polynomial algebra over `R` is allowed. Its underlying module may be
  infinitely generated, so finite type has not been replaced by module-finiteness.
- The base may be nonreduced or disconnected. No reducedness, domain, locality,
  characteristic, or nontriviality hypothesis was introduced.
- The common-universe lifts preserve the canonical fibre and do not equate the
  independent ring universes or make the field-extension quantification vacuous.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query "Noetherian finite type flat algebra with
  geometrically integral fibres is projective as a module": eight hits including
  `Algebra.Smooth.flat_of_isNoetherianRing` and
  `Module.Flat.projective_of_finitePresentation`; no exact statement.
- `msearch.py loogle`, query
  `Module.Projective, Algebra.FiniteType, RingHom.Flat, IsNoetherianRing`: zero hits.
- `msearch.py leansearch`, the same natural-language query: eight hits, including
  the module-finite-presentation flat-to-projective result; no exact statement.
- `msearch.py grep`, query
  `geometric.*integral.*projective|projective.*geometric|fibres-irreducible-flat-projective`:
  zero Mathlib hits.
- `rg` in `WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json`
  for the item id, fibre/projectivity, geometric integrality, and Noetherian
  projectivity: no existing theorem for this exact Noetherian finite-type case.
  The side library has `Algebra.projective_of_geometricallyIntegral_fibres` in
  `Sheaf.RingTheory.AffineGeometricallyIntegralProjective`. Its full declaration
  was read: it is the non-Noetherian finite-presentation theorem, with a different
  field-test interface. It is not this node and is not used to bypass its proof.
  `LocalNoetherianApproximation` was also read for the existing `Ideal.Fiber` and
  geometric-integrality interface; no private fibre definition was introduced.
- Direct source reads checked `Ideal.Fiber`, `RingHom.ulift`, and
  `Spec.residueFieldIso`, including their full signatures and docstrings.

Node metadata issue: the `source.place` says Tag 05FT but names the Noetherian
lemma label. The local Stacks tag table assigns that label Tag 05FS and assigns
05FT to the non-Noetherian finite-presentation variant. The statement and the
node's existing proof source places already agree with 05FS. The module cites
05FS; no mathematical statement correction or unrelated metadata edit is made.
No STATEMENT-DISPUTED issue was found.

## Dependency modules

`lem-trf-local-projective-faithfully-flat-descent`: the recorded module
`Sheaf.TraceFormula.LocalProjectiveFaithfullyFlatDescent` had no `module` header.
The first prescribed compile rejected importing it from the item's `module` file:
"cannot import non-`module` Sheaf.TraceFormula.LocalProjectiveFaithfullyFlatDescent
from `module`". The current published source was confirmed with
`scompile.py --source`. Section 1(B) repairs this interface in the same delivery:
the dependency module retains its declaration name, complete theorem signature,
existing docstring and `sorry` proof, and gains the module header, public imports
of its three statement dependencies, and an exposed public section. The added
copyright header records the original group Q32 and this group's format repair.
Only its node's `lean` record changes, with the exact signature, date, group and
an explanatory `lean.note`. Its statement, dependencies, and proof plan stay
unchanged. It is already a proof prerequisite of the item, so no DAG edge is added.

## Second reading by NH

Author's self-check for direct delivery; no independent worker was started.
The maintainer supplies the independent review under the direct-delivery brief.
With both node JSON files and both Lean files open, I rechecked each binder and
conclusion against the correspondences above. The main theorem has exactly
Noetherianity, finite type, flatness, and geometric integrality for each actual
canonical fibre; its conclusion is projectivity of `S` over `R`. I checked the
universe arguments and the residue-field/fibre isomorphisms explicitly. For the
descent dependency, the theorem signature and docstring are unchanged; only
module-format commands and the copyright header were added. The first compile
found the legacy dependency import mismatch, which this dependency repair fixes.
There is one `sorry` for each existing DAG statement and no proof or definition
with postponed data. Validation uses the prescribed per-file compilation and
preflight through `deliver2.py`; every delivered file is compiled separately.
