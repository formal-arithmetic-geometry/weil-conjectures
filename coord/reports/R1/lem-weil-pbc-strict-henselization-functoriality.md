## Worker report

The module defines `AlgebraicGeometry.strictHenselizationFunctoriality` in
`lean/Sheaf/Paper/StrictHenselizationFunctoriality.lean`. It states the source
setup with schemes `S,T`, a morphism `g`, algebraically closed geometric-point
field `Ω`, points `barT` and `barS`, and the compatibility equation `hbar`.
The conclusion existentially supplies local-ring instances for both strict
henselization rings, asserts `IsStrictlyHenselianLocalRing` for each using the
project definition, and asserts existence and uniqueness of a ring morphism
whose underlying ring map is local. Every proof is `sorry`.

The strict henselization construction comes from
`Sheaf.AlgebraicGeometry.StrictHenselization` (`Scheme.strictHenselizationRing`),
and strict henselian terminology from
`Sheaf.RingTheory.HenselianTerminology` (`IsStrictlyHenselianLocalRing`).
Scheme and geometric-point primitives use Mathlib `Scheme`, `IsAlgClosed`, and
`Scheme.Spec`; residue-field and fibre-product dependencies were checked from
their recorded Mathlib declarations. The dependency node
`def-weil-pbc-strict-henselization-limit` is included with its recorded module
because the construction is project-specific and not available in Mathlib.

Edge cases checked include arbitrary universe `u`, arbitrary algebraically
closed `Ω`, and no characteristic, nonemptiness, or finiteness assumptions.
Searches reviewed: `msearch.py` LeanFinder and Loogle queries for strict
henselization/functoriality, grep of Mathlib and `WeilConjectures`; no exact
existing theorem was found. The file compiles cleanly with `scompile.py`.

## Dependency modules

`def-weil-pbc-strict-henselization-limit` uses the dependency module
`Sheaf.AlgebraicGeometry.StrictHenselization` and its declaration
`AlgebraicGeometry.Scheme.strictHenselizationRing` (plus the associated
construction declarations in that module).

## Earlier second reading (a previous round; superseded)

I re-read every hypothesis and conclusion clause against the node and module:
`g`, `barT`, `barS`, and `hbar` are explicit; both local-ring existential
binders and both strict-henselian assertions are present; the final `∃!`
quantifies exactly a morphism of the two strict henselization rings and states
its locality. No source clause was silently strengthened or dropped.


## Second reading by R1

I opened the complete item node, both delivered Lean modules, and every statement
dependency node. I read the recorded project definitions and the Mathlib signatures
for Scheme, SpecToEquivOfField, residueField, residueFieldMap, separableClosure,
pointSmallEtale, AffineEtale.Spec, Functor.Elements, pullback and locally ringed
space morphisms. There is no statement correction: the node's four clauses are
correct. The previous round's claim of an exact match was wrong.

Source reading: this clone has no Stacks .tex checkout. I fetched the upstream
etale-cohomology.tex and algebra.tex into the sandbox scratchpad and read
etale-cohomology.tex lines 4250-4354 (04HX, 03PS, and its following paragraph),
algebra.tex lines 43369-43400 (04GU) and 43509-43536 (08HV), and the inclusion
at etale-cohomology.tex line 18694 in the proof of 095T. These assume schemes,
a geometric point, and its residue embedding; no Noetherian, finite type,
separatedness, or characteristic restriction occurs. I also read the online tags
https://stacks.math.columbia.edu/tag/04HX, /03PS, /04GU and /08HV.

Object/hypothesis/conclusion inventory and matching:

1. Schemes S,T and a scheme morphism g: `{S T : Scheme.{v}} (g : T ⟶ S)`.
   Verdict: exact, with Mathlib Scheme and its category.
2. An algebraically closed field Ω and geometric points barT, barS with
   barS = g composed with barT: `[Field Ω] [IsAlgClosed Ω]`, the two Spec
   morphisms, and `hbar : barS = barT ≫ g`. Verdict: exact; t and s are
   `barT (IsLocalRing.closedPoint Ω)` and `barS (IsLocalRing.closedPoint Ω)`.
3. Arbitrary Y and barY in clause (1): `strictHenselizationResidue` quantifies
   over `{Y : Scheme.{v}}` and `barY`. Verdict: covers every Y, not only S,T.
4. Strict henselization rings and schemes: the existing
   `Scheme.strictHenselizationRing` and `strictHenselizationScheme` throughout.
   Verdict: the chosen small-model colimit and its spectrum are unchanged.
5. Every affine pointed neighbourhood and its canonical projection c_V:
   `Scheme.strictHenselizationNeighbourhoods` and the added
   `Scheme.strictHenselizationProjection`. Verdict: exact. These are spectra
   of rings, not a restricted selection of affine schemes; the recorded
   `strictHenselizationAffineInclusion_isEquivalence` identifies them with the
   full affine subcategory. The projection at n uses the inverse unit map
   from the representative of n to n, then contravariant global sections,
   the representative colimit coprojection, Spec.map, and isoSpec.inv.
6. Canonical j_Y: the existential j in `strictHenselizationResidue`, with
   `∀ n, strictHenselizationProjection barY n ≫ n.1.hom = j`.
   Verdict: exactly the common composite specified in the node. The data
   jS,jT and hcS,hcT in the second theorem are these same canonical maps.
7. The geometric-point extension κ(y) → Ω: the Algebra instances and hΩ
   (respectively hΩS,hΩT) equate their algebraMap to
   `Scheme.descResidueField (Scheme.stalkClosedPointTo barY)`.
   Verdict: these encode the extension through the geometric point required
   by the node; arbitrary unrelated algebra structures are not admitted.
   Such a structure always exists by RingHom.toAlgebra, so no extra
   mathematical assumption is introduced.
8. κ(barY) is the relative separable closure inside Ω:
   `separableClosure (Y.residueField (barY (closedPoint Ω))) Ω`.
   Verdict: uses the dependency's exact Mathlib notion (carrier IsSeparable),
   rather than a separately chosen abstract separable closure.
9. Clause (1), strict henselian local ring: existential IsLocalRing followed
   by `IsStrictlyHenselianLocalRing` in strictHenselizationResidue.
   Verdict: exact, including both HenselianLocalRing and IsSepClosed of its
   quotient residue field, as the recorded terminology definition states.
10. Clause (1), closed point maps to y: the equality involving j and
    `IsLocalRing.closedPoint (strictHenselizationRing barY)`.
    Verdict: restored; it was absent from the worker's statement.
11. Clause (1), unique residue identification and all factorizations:
    `∃! σ : IsLocalRing.ResidueField ... ≃+* separableClosure ...`, with
    every n's pointed lift equal to Spec of the inclusion composed with σ
    and the residue quotient, followed by its canonical projection.
    The subsequent equation with j is the factorization of barY itself.
    Verdict: exact. σ is written as a ring equivalence; its compatibility
    with all affine pointed neighbourhoods forces κ(y)-linearity. Indeed,
    restrict to affine neighbourhoods around y, then pass to the local
    ring and its residue field. Conversely a κ(y)-algebra isomorphism with
    the node's factorizations satisfies these equations. The kernel of
    the composite quotient, σ and inclusion is the maximal ideal, so the
    second spectral map is precisely the closed point. This restores the
    essential uniqueness condition, which the worker omitted.
12. Clause (1), κ(barY) separably closed: explicit `IsSepClosed` of the
    relative closure in strictHenselizationResidue. Verdict: restored.
13. Clause (2), inclusion inside Ω: `∀ x : Ω, x ∈ separableClosure ...S... →
    x ∈ separableClosure ...T...`. Verdict: exact subset relation on the
    actual embedded fields, not just existence of an abstract field map.
14. Clause (3), existence, locality, base diagram and residue inclusion:
    existential h, `IsLocalHom h.hom`, `Spec.map h ≫ jS = jT ≫ g`, and
    equality of the two ring maps from the S-ring to Ω.
    Verdict: exact. Since the quotient maps are surjective and the
    identifications/inclusions are injective, this last equality is
    equivalent to the residue map being the inclusion of clause (2).
15. Clause (3), uniqueness: the explicit `∀ h'` has exactly locality,
    the base diagram, and that residue equality as premises, then h'=h.
    Verdict: repaired. The original `∃! h, IsLocalHom h.hom` incorrectly
    claimed uniqueness of every local ring map, even those not respecting
    either diagram or residue embedding. Neighbourhood compatibility is
    not added to the uniqueness premises.
16. Clause (4): all nS,nT, every scheme morphism w of their underlying
    schemes, the base compatibility and pointed-lift compatibility imply
    `strictHenselizationProjection barT nT ≫ w =
      Spec.map h ≫ strictHenselizationProjection barS nS`.
    Verdict: restored in full. It is not restricted to a fibre-product
    example; that example is covered by these universally quantified data.

Presentation and quantifiers: two declarations realize the node. The first
supplies clause (1) without any local-ring assumption, for arbitrary Y.
The second is uniform over all choices of the local-ring proofs, canonical
maps and residue identifications supplied by the first, and establishes
clauses (2)-(4). Thus its explicit canonical-data premises do not replace
existence by an assumption; existence and uniqueness are in the first
declaration. No theorem is proved: every theorem proof is `by sorry`.
The proof docstrings now carry all nine node proof steps and their citations,
including the affine reduction, separable closure, triples, factorization,
inclusion, lifting, uniqueness and neighbourhood compatibility arguments.

Edge cases: any universe v is allowed, and all objects use the recorded
Scheme/CommRingCat universe. The same-universe Ω agrees with the dependency's
construction and Mathlib's geometric-point equivalence; larger input objects
are covered by enlarging v. Empty S or T cannot have a geometric point from
Spec of a field, so no nonempty scheme assumption is needed. The pointed
neighbourhood category is nonempty/cofiltered by the recorded construction;
there is no imposed finite or nonempty index set. A zero strict henselization
ring would contradict the residue-field identification, correctly excluded
by the theorem's conclusion, not by a new hypothesis. There is no integer n,
characteristic restriction, finite type condition or Noetherian hypothesis.

Independent searches: LeanFinder query "etale stalk residue field separable
algebraic closure canonical map" found descResidueField, residueFieldMap and
fromSpecResidueField, not this theorem or strict-henselization projections.
Loogle query `"strictHensel"` returned no hits. LeanSearch query "strict
henselization canonical affine neighbourhood projections" was unavailable
(HTTP internal server error), recorded rather than treated as a negative
result. Grep using henselization/Henselization and strictHensel in Mathlib,
WeilConjectures and lean/Sheaf found the shared StrictHenselization module,
ring-level IsStrictHenselization and its Noetherian/flatness results, but no
geometric-point functoriality theorem or arbitrary-neighbourhood projection.
I also searched DAG node text for canonical projections: the notion belongs
to def-weil-pbc-strict-henselization-limit, so no new definition node is added.

Dependency module review: the original StrictHenselization file accurately
constructs the small-model colimit, spectrum and representative cone, but
has no exposed projection to an arbitrary affine pointed neighbourhood.
I preserved its definitions and statements verbatim and added only that
projection in its own namespace with source and blueprint docstring. Its
data is built directly from the existing colimit and equivalence, with no
sorry. The dependency lean record names the added declaration and explains
this missing interface. The original dependency-module report is superseded
by this precise account; there were no new nodes or private copies.

Every mismatch identified above is repaired in Lean, not by changing the
node's mathematical statement. The node lean.statement is the main
signature verbatim; lean.declarations lists both statements. The dependency
record similarly matches its file. All variables and universes are bound,
and there are no file-local definitions, notations or instances.

Validation: scompile.py compiled both modules together against the server library
in 3.5 seconds with exit code 0 and no warnings. deliver2.py --no-push
printed OK: the delivery compiles and passes the preflight (87ddffa26).
