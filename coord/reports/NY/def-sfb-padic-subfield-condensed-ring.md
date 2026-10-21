## Worker report

Existing declaration: `Profinite.padicSubfieldCondensedRing` in
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`, lines 91–108.
No module is added. The node is attached to this existing construction, together
with `Profinite.padicCondensedRingToPadicSubfieldCondensedRing` and the underlying
commutative ring-object declarations. Only the item's `lean` record changes.

Read the complete node, its three statement dependencies and their recorded
modules, the current blueprint's `def-sfb-padic-subfield-condensed-ring.md` and
`.proof.md`, and the upstream implementations. No repair note exists for this
item. The supplied CompactObject example module is withdrawn; its actual
recorded upstream module was read instead.

Hypotheses and clauses, in source order:

- Prime ℓ: `(ℓ : ℕ) [Fact ℓ.Prime]`. The ambient field is Mathlib's
  `PadicAlgCl ℓ`, the algebraic closure with the norm extending the p-adic norm
  (`PadicAlgCl.norm_extends`). This is a fixed model of the algebraic closure
  in the source, not its completion `PadicComplex`.
- A field with an embedding: `(E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]`.
  The specified embedding is `algebraMap E (PadicAlgCl ℓ)`; its injectivity
  follows from the field domain. Conversely every ring embedding into this
  commutative field supplies exactly this algebra structure. No ℚℓ-extension,
  completeness or finite-dimensionality is imposed at this stage.
- Restricted absolute value: the definition installs
  `PadicAlgCl.normedFieldOfAlgebra ℓ E`. Read
  `WeilConjectures.NumberTheory.Padics.Extension`, lines 134–144: it is
  `NormedField.induced E (PadicAlgCl ℓ) (algebraMap E (PadicAlgCl ℓ)) ...`.
  Thus `‖x‖ = ‖algebraMap E (PadicAlgCl ℓ) x‖` by definitional equality.
  Its topology is definitionally
  `TopologicalSpace.induced (algebraMap E (PadicAlgCl ℓ)) inferInstance`.
  The normed field structure supplies continuous addition, multiplication,
  negation and inversion away from zero.
- Condensed ring: after installing that norm, the abbreviation is
  `Profinite.continuousMapRingSheaf E`, definitionally the recorded dependency
  `Profinite.continuousMapRingSheafOfUniverse.{u, 0} E`. Its category is
  `Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}`.
- Sections: at `S : Profinite.{u}ᵒᵖ`, its section ring is definitionally
  `RingCat.of (ULift.{u + 1} C(S.unop, E))`. `ULift` only implements the site's
  coefficient size convention. Operations are pointwise. Restriction along
  `f : S ⟶ S'` is `a ↦ ULift.up (a.down.comp f.unop.hom.hom)`.
- Underlying commutative ring object: `Profinite.continuousMapRingObj E`
  is the actual underlying abelian sheaf; with the restricted norm installed,
  `Profinite.isCommMonObj_continuousMapRingObj E` supplies commutativity.
  Also checked the dependency's explicit `sfbSheafTensorStructure` version,
  using `Profinite.continuousMapRingObjOfUniverseMonObj` and
  `Profinite.isCommMonObj_continuousMapRingObjOfUniverse`, on the same
  underlying sheaf. No unrelated ring-object structure is substituted.
- Conditional ℚℓ-extension and ℚℓ-linear embedding: additional instances
  `[Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]` appear only on
  `Profinite.padicCondensedRingToPadicSubfieldCondensedRing`. The tower says
  exactly that the embedding respects the ℚℓ-structure maps.
  `AlgebraicGeometry.ProEtale.continuous_algebraMap_padic_of_algebra ℓ E`
  proves continuity for this restricted topology; its source and full proof
  were read in `WeilConjectures.CategoryTheory.RingObjects.EllAdic`,
  lines 180–190.
- Coefficient arrow: the existing morphism has source
  `Profinite.padicCondensedRing ℓ`, the exact recorded dependency, and target
  `Profinite.padicSubfieldCondensedRing ℓ E`. It is definitionally
  `Profinite.continuousMapRingSheafMapOfUniverse.{u, 0}` applied to
  `algebraMap ℚ_[ℓ] E` and the preceding continuity proof. Its component
  satisfies `(map.app S a).down s = algebraMap ℚ_[ℓ] E (a.down s)` by
  definitional equality, precisely postcomposition.

Dependency declarations used:

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`,
  `Profinite.continuousMapRingObjOfUniverse`,
  `Profinite.continuousMapRingObjOfUniverseMonObj`,
  `Profinite.isCommMonObj_continuousMapRingObjOfUniverse`.
- `Sheaf.Topology.ContinuousMapCondensedRingMap`:
  `Profinite.continuousMapRingSheafMapOfUniverse`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicCondensedRing`, the existing subfield ring and coefficient
  arrow. Its imported `Condensed.ContinuousMap` supplies
  `Profinite.continuousMapRingObj` and its commutativity instance.

Edge cases and sizes: the general ring needs only the field embedding, so
subfields not containing ℚℓ (for example the prime field) remain allowed.
Neither infinite extensions nor the full algebraic closure are excluded;
no local compactness, completeness or finiteness is assumed. All primes,
including 2, are allowed. A zero ring is excluded by the source's field
hypothesis. Empty profinite sets give the singleton ring of functions;
precomposition and postcomposition also work there. At E = ℚℓ with its
canonical embedding the coefficient arrow is the expected identity after
identifying the restricted norm. The profinite universe u is arbitrary and
independent of the field representation. The existing upstream API uses a
small field model `E : Type`: this covers every mathematical subfield of
`PadicAlgCl ℓ`. Explicitly, for any `F : Type v` with an embedding
`ι : F →+* PadicAlgCl ℓ`, `small_of_injective ι.injective : Small.{0} F`
was checked by the server. Thus even a larger representation has a small
copy (its image subfield) preserving its restricted norm and topology;
this size convention excludes no embedded field.

Searches performed, all through the prescribed tools or direct source reads:

1. `msearch.py ... leanfinder`, query “A field embedded in an algebraic closure
   of the p-adic numbers inherits the restricted norm topology and a condensed
   ring of continuous maps”: eight hits, including `PadicAlgCl.normedField`,
   `PadicAlgCl`, `PadicAlgCl.norm_extends`; no full condensed-ring declaration
   in Mathlib.
2. `msearch.py ... loogle`, query
   `PadicAlgCl.normedFieldOfAlgebra, Profinite.padicSubfieldCondensedRing`:
   zero hits, unknown identifier `PadicAlgCl.normedFieldOfAlgebra`. These are
   project names, not Mathlib names; this search alone does not show absence.
3. `msearch.py ... grep`, query
   `normedFieldOfAlgebra|padicSubfieldCondensedRing|continuous_algebraMap_padic_of_algebra`:
   zero Mathlib hits.
4. `msearch.py ... leansearch`, query “Condensed ring associated to a subfield
   of the algebraic closure of the p-adic numbers”: eight hits on
   `PadicAlgCl`, its algebraicity, `PadicComplex`, `PadicInt.subring`, and
   basic p-adic ring instances; no condensed-ring construction.
5. Direct `rg` on `lean/WeilConjectures`, `lean/Sheaf` and
   `dag/lean_names_upstream.json` for the names above found the exact existing
   construction in `Condensed/EllAdic.lean:97`, the coefficient arrow at
   lines 105–108, restricted norm in `Padics/Extension.lean:142`, and
   continuity in `RingObjects/EllAdic.lean:184`. Numerous Sheaf consumers use
   this same upstream object. The name index had no additional match.
6. Direct `grep -rn` for the node id in `lean/WeilConjectures` gave no hit;
   direct `rg` for `padicSubfieldCondensedRing|padic-subfield-condensed-ring`
   in Mathlib's Condensed directory and `lean/Sheaf/Topology` gave no match.
   The exact upstream declaration was located by name, not blueprint id.

Validation: `Validation.lean` is a scratch consumer outside the delivered
`lean/` tree. It imports the existing upstream module and the recorded
continuous-map dependency modules, with auto-implicit binding disabled. It
checks the full existing signatures, norm, induced topology, identification
with the recorded sheaf, lifted sections, restrictions, both commutativity
interfaces, exact coefficient-map identification, its sectionwise formula,
and smallness of an arbitrarily large embedded field. It is compiled only
through `scompile.py`; it is not a new statement module or part of delivery.
An initial scratch-only letI style warning was fixed by using `let`.

No statement correction, new node, dependency repair, hollow definition,
or statement dispute is needed. The maintainer supplies the independent review.

Final scratch validation passed with exit code 0, no warnings, in both the
sandbox and library-context compiles (5.4 s and 5.8 s). The explicit
commutativity check specializes the dependency's universe-polymorphic
commutativity theorem at `.{u, 0}`; a separate definitional-equality check
identifies its underlying abelian sheaf with the upstream one. This avoids
an underdetermined sheaf-tensor size metavariable in an earlier scratch type.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
