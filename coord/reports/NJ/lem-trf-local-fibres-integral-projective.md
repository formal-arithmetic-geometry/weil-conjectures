## Worker report

The module `Sheaf.RingTheory.GeometricallyIntegralFibersProjective` states
`Module.projective_of_flat_of_finitePresentation_of_geometricallyIntegral_fibers`,
with `sorry` as its only proof. It states Stacks Tag 05FT, read in
`literature/stacks-project/flat.tex`, lines 2246–2278. No definition, new node,
dependency repair, or statement correction is needed.

Hypothesis and conclusion correspondence:

- “Commutative rings R and S, R → S” is `{R : Type u} {S : Type v}
  [CommRing R] [CommRing S] [Algebra R S]`, with the given map `algebraMap R S`.
  The universes `u` and `v` are independent; no same-universe restriction is
  imposed. Universally quantified algebra structures cover every ring homomorphism
  via `RingHom.toAlgebra`. No finite cardinality, nontriviality or field assumption
  is imposed on either ring.
- “Finitely presented” is `hfp : RingHom.FinitePresentation (algebraMap R S)`.
  Its definition in Mathlib is exactly `Algebra.FinitePresentation` for this
  map's algebra structure. It does not assert finite presentation as a module.
  `LocallyOfFinitePresentation.SpecMap_iff` identifies this with the recorded
  scheme dependency on affine spectra.
- “Flat” is `hflat : RingHom.Flat (algebraMap R S)`, the recorded dependency.
  `RingHom.flat_algebraMap_iff` identifies it with `Module.Flat R S`.
- “For every prime of R” is `∀ p : PrimeSpectrum R` in `hgeom`.
- The fibre ring is the existing `p.asIdeal.Fiber S`, defined by Mathlib as
  `p.asIdeal.ResidueField ⊗[R] S`. Tensor symmetry identifies this with the
  source's `S ⊗[R] κ(p)`. No custom fibre ring is introduced.
- “Geometrically integral over κ(p)” is
  `GeometricallyIntegral (Spec.map (CommRingCat.ofHom
  ((algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)).comp
    (ULift.ringEquiv (R := p.asIdeal.ResidueField)).toRingHom)))`.
  The `ULift.ringEquiv` is the canonical universe transport: it lifts the residue
  field to the fibre's `max u v` universe before applying the canonical coefficient
  map, so `CommRingCat.ofHom` has one object universe. This uses the actual spectrum
  of the fibre ring and the recorded geometric-integrality class. The class's
  definition and `geometrically_iff_of_commRing` test every field extension in the
  scheme universe, including the identity extension. Thus nonempty integral fibres,
  as well as reducedness and irreducibility, are required.
- The entire conclusion is `Module.Projective R S`, exactly the recorded
  projective-module notion, for the same algebra structure.

Dependency declarations read and used, with their modules:

- `RingHom.Flat`, `Module.Flat`:
  `Mathlib.RingTheory.RingHom.Flat` (and its public imports).
- `Module.Projective`: `Mathlib.Algebra.Module.Projective`.
- `AlgebraicGeometry.LocallyOfFinitePresentation` and its affine criterion
  `LocallyOfFinitePresentation.SpecMap_iff`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
  Its public imports provide `RingHom.FinitePresentation`.
- `AlgebraicGeometry.Scheme.residueField`,
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`:
  `Mathlib.AlgebraicGeometry.ResidueField`. For affine ring fibres, the
  equivalent ring residue field is Mathlib's `Ideal.ResidueField`, used by
  `Ideal.Fiber` in `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`.
- `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`:
  `Mathlib.AlgebraicGeometry.Scheme`, publicly imported by the geometry modules.
- `AlgebraicGeometry.GeometricallyIntegral`:
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`.

The two unstated proof dependencies `lem-trf-local-noetherian-approximation`
and `lem-trf-local-noetherian-fibres-projective` have no Lean modules to import.
The stated Mathlib proof dependencies are imported:
`Module.Projective.tensorProduct` in `Mathlib.Algebra.Module.Projective`, and
`Algebra.FiniteType.isNoetherianRing` in `Mathlib.RingTheory.FiniteType`.
The docstring records all three DAG proof steps: Noetherian approximation,
Noetherian projectivity, and scalar extension followed by transport.

Edge cases checked against the statement and source:

- If R is the zero ring then an R-algebra S is zero, there are no primes, and
  the conclusion correctly says that the zero module is projective.
- If R is nonzero and S is zero, the nonempty spectrum required by geometric
  integrality excludes the example. The identity field extension is included.
- For `k[x]` over a field k the algebra is finitely presented and has integral
  geometric fibre and is free, despite being infinite dimensional over k.
  This checks that module-finiteness has not been inserted.
- `ℤ[1/2]` over ℤ is flat and finitely presented as an algebra but has empty
  fibre at (2), so it is correctly excluded. No surjectivity hypothesis was
  separately added.
- A reducible or nonreduced geometric fibre fails `GeometricallyIntegral`.
  No Noetherian, local, or domain assumption is added on the base ring.

Searches made with the prescribed wrapper (complete machine responses in
`searches.jsonl`):

- LeanFinder: “A flat finitely presented algebra whose fibres are geometrically
  integral is projective as a module over its base ring”: 8 hits, including
  `Module.Flat.projective_of_finitePresentation` and
  `Algebra.FormallyUnramified.projective_of_restrictScalars`; no exact match.
- Loogle: `Module.Projective, RingHom.Flat`: 0 hits.
- LeanSearch: “flat finitely presented algebra geometrically integral fibres
  projective module”: 8 hits, chiefly the module finite-presentation theorem,
  `RingHom.Flat`, and localization projectivity; no exact match.
- Wrapper grep: `fibres-irreducible-flat-projective|geometrically.*integral`
  in `AlgebraicGeometry`: 14 hits in geometric-integrality files, no projectivity
  theorem. Direct Mathlib search found no algebra geometric-integrality
  projectivity result. Reading `Module.Flat.projective_of_finitePresentation`
  confirms it requires `Module.FinitePresentation`, so it is not this theorem.
- Direct `rg` of the upstream `WeilConjectures` for `05FT`, geometric-integral
  fibres and projectivity found only unrelated geometry; direct search for the
  item id returned no match. The new declaration name also returned no match
  in Mathlib, upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json`.
- Direct `rg` of `lean/Sheaf` found the geometric fibre predicates in other
  statements, but no statement of Tag 05FT. The DAG's
  `lem-trf-affine-geometrically-integral-projective` is a known duplicate
  mathematical node, but has neither `lean` nor `mathlib_match`; there is no
  existing declaration to reuse. This delivery states only the assigned node.

No statement dispute or node fault was found. Compilation and the prescribed
preflight are run before delivery; expected `sorry` is intentional in stage 2.

## Repair self-check

The returned entry for immutable head `d46076fecd14` reports that the
maintainer's `--apply-fixes` rejected a report path outside its permitted fix
packet layout. This repair uses the normal worker delivery layout: this
`report.md` is packaged by `deliver2.py` at the prescribed report destination.
The initial dry run on the retained packet passed preflight and per-file
compilation (commit `1ce991ecbc`); no mathematical or Lean repair was requested
by that diagnostic.

I reread the saved module and node against the current shared base. The node
copy differs only in `lean`, and its recorded signature matches the file
verbatim. Every line is at most 100 characters; the universe and all binders
are explicit. I reread Tag 05FT in `flat.tex` and the recorded dependency
signatures and docstrings: finite presentation is algebra finite presentation,
flatness is for the given algebra map, every prime is tested, geometric
integrality applies to the canonical spectrum of `κ(p) ⊗[R] S`, and the
conclusion is projectivity of the same R-module S. The zero-ring and empty
fibre cases remain as checked above. No hypothesis, conclusion, dependency,
definition, or proof was changed. The report is the only repair-content change;
the retained Lean statement is delivered through the normal packet rather
than a maintainer `--apply-fixes` directory.

## Second reading by NJ

Independent maintainer second reading, 2026-10-18, immutable delivery
`de470637f9c70df6646dba9be37266474149436b`.

The delivered theorem agrees with the node and Stacks flat.tex 2246–2278,
Tag 05FT, clause by clause. Commutative rings and the given map are the
independent-universe R, S and their Algebra structure. RingHom.FinitePresentation
means algebra finite presentation, not module finite presentation. RingHom.Flat
means flatness of S with precisely that scalar action. Every PrimeSpectrum R
point is tested. Ideal.Fiber S is the canonical residue-field tensor product;
tensor symmetry matches the source's order. Spec.map uses the canonical
coefficient homomorphism, precomposed with ULift.down as a ring equivalence.
GeometricallyIntegral tests integral pullbacks under every field extension,
including the identity. The entire conclusion is Module.Projective R S.
All binders and universes are bound; the signature equals lean.statement verbatim.

All six immutable statement dependencies and their exact Mathlib declarations
and docstrings were read. The affine residue-field identification is
Scheme.Spec.residueFieldIso; LocallyOfFinitePresentation.SpecMap_iff supplies
the affine finite-presentation criterion. Projectivity is the splitting of the
canonical free-module surjection. No private or hollow definition occurs.
The module and theorem docstrings name the source and blueprint, and carry
all three proof steps: approximation, Noetherian projectivity, tensor base change.
Its only proof is sorry. The two source-theorem proof prerequisites were not
statement prerequisites and did not need to be assumed in the theorem.

Edge cases: zero R forces zero S and an empty prime index; this gives the
projective zero module. Zero S over nonzero R, and empty fibres such as the
fibre of Z[1/2] at (2), fail geometric integrality. Geometrically reducible and
nonreduced fibres are excluded. Polynomial algebras over fields are included;
no module-finiteness, Noetherian base, characteristic, domain-base or local-base
restriction is present. Both independent universes are retained by the lift.
Testing fields in max u v suffices for affine geometric integrality: any failure
in a larger field is witnessed by finitely many coefficients and descends to a
field of that size. The same argument applies to the existing binding below.

Findings and corrections:

- H4: contrary to the worker's search claim above, the delivery's own parent
  already contains Sheaf.RingTheory.AffineGeometricallyIntegralProjective,
  Algebra.projective_of_geometricallyIntegral_fibres. Direct searches of Mathlib,
  upstream WeilConjectures and the side library found this exact mathematical
  statement. Module.Flat.projective_of_finitePresentation is a different theorem
  requiring finite presentation as a module. The existing Tag 05FT theorem
  quantifies over each residue-field map to K, with the induced R-action fixed
  by its equality premise, and requires IsDomain (B tensor_R K). By tensor
  associativity, affine pullbacks and Spec-domain integrality this is exactly
  the geometric fibre condition. The identity extension is included. Its
  conclusion is Module.Projective R B. The corrected lean record reuses this
  declaration with existing:true and file:null; merge_delivery automatically
  omits the newly delivered duplicate module. No extra theorem or dependency
  edge is introduced. The node's existing noncircular three-step proof plan
  remains the proof plan for the shared statement.
- H11: the original section explicitly recorded no reading. This complete
  replacement report supplies the actual independent second reading while
  preserving the worker report and distinguishing its inaccurate search claim.

Compiler reproduction: scompile.py NJ lem-trf-local-fibres-integral-projective
on the immutable delivered file returned 0, no diagnostics; sandbox 6.4 s,
library 2.3 s. The wrapper in this environment uses the server-confirmed private
side overlay. No direct ssh, global build, live Lean write, or Git mutation was
performed. The existing binding was separately compiled through scompile.py: return code 0,
no diagnostics, sandbox 1.9 s and library 2.4 s.
The route-pivot dropped list contains none of the item's statement or proof
citations; no item route-pivot repair note exists at origin/newtargets-dag.
This commutative algebra statement uses no dropped machinery or pro-etale
substitute. No source-based statement correction or citer audit was necessary.
