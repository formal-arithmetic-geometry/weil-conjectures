## Worker report

The module Sheaf.RingTheory.EtaleContractionProperties states
CommRingCat.etaleContraction_properties, with the whole proof `sorry`.
The node statement and all other node fields are unchanged. No new notions or nodes
are needed, and no statement fault or dispute was found.

Clause-by-clause correspondence:

- A commutative ring R is `(R : CommRingCat.{u})`; the bundled object includes its
  commutative ring structure, with no nonzero, local, or noetherian hypothesis.
- Rᵉ is precisely `R.etaleContraction`, the recorded construction of
  def-weil-pbc-etale-contraction. The canonical structural map R → Rᵉ is
  `(EtaleContraction.ι R 0).hom`; `stage (op R) 0` reduces to `op R`.
- Faithful flatness is the first conjunct, that map's `RingHom.FaithfullyFlat`.
- Ind-étaleness is the second conjunct, that map's `RingHom.IndEtale`. This is the
  ring-map form of the recorded `Algebra.IndEtale`, using the canonical map's
  algebra structure, not an arbitrary action on the contraction.
- Every commutative algebra over Rᵉ is quantified as `(B : Type u) [CommRing B]
  [Algebra R.etaleContraction B]`. This uses the fixed universe stipulated by
  the contraction definition, and covers the full range of algebras of that size.
- The three hypotheses on B are explicitly `Module.FaithfullyFlat`,
  `Algebra.Etale`, and `Algebra.FinitePresentation` over Rᵉ.
  Algebra.Etale is the affine ring-map counterpart of the recorded scheme notion:
  Mathlib's Etale HasRingHomProperty instance identifies it with the étaleness of
  Spec of the algebra map. Finite presentation is retained explicitly even though
  it also follows from Algebra.Etale.
- A section is `Nonempty (B →ₐ[R.etaleContraction] R.etaleContraction)`.
  For any such ρ, AlgHom.commutes says ρ(algebraMap s) = s, since the target
  Rᵉ-algebra is the identity algebra. Thus it is precisely a retraction of the
  structural ring map, or equivalently a section of the induced affine scheme map.
  No chosen section, uniqueness, or extra conclusion is asserted.
- Every maximal localization is the last conjunct: `(m : Ideal R.etaleContraction)
  [m.IsMaximal]` and `IsStrictlyHenselianLocalRing (Localization.AtPrime m)`.
  The maximal-ideal instance supplies primality for the existing localization.

Dependency declarations read and used:

- Sheaf.RingTheory.EtaleContraction: CommRingCat.etaleContraction and
  CommRingCat.EtaleContraction.ι (also read Representatives, finiteDiagram, step,
  stage, and sequence to check the exact construction and initial structural map).
- Sheaf.RingTheory.IndPrincipalZariski publicly exposes the recorded Algebra.IndEtale
  from WeilConjectures.RingTheory.ProEtale.IndEtale. Its ring-map form is
  RingHom.IndEtale, which uses f.toAlgebra.
- WeilConjectures.Mathlib.RingTheory.Henselian: IsStrictlyHenselianLocalRing,
  extending HenselianLocalRing with separably closed residue field.
- Mathlib.RingTheory.Flat.FaithfullyFlat.Basic: Module.FaithfullyFlat;
  Mathlib.RingTheory.RingHom.FaithfullyFlat: RingHom.FaithfullyFlat.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: AlgebraicGeometry.Etale and its
  HasRingHomProperty instance; Mathlib.RingTheory.Etale.Basic: Algebra.Etale.
  The scheme module is publicly exposed by the contraction dependency.
- Mathlib.RingTheory.FinitePresentation: Algebra.FinitePresentation.
- Mathlib.RingTheory.Localization.AtPrime.Basic: Localization.AtPrime.

The module also imports the already stated proof dependencies without `public`:
Sheaf.RingTheory.IndEtaleStability, Sheaf.AlgebraicGeometry.LimitAffineTransition,
Sheaf.Paper.EtaleFiniteDataDescent, the Mathlib affine-limit, affine permanence,
separatedness, finite coproduct and tensor universal-property modules, and
WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian for
IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction.
The directed-colimit-faithful-flatness node has no recorded module, so no import
can yet be supplied for it. No import cycles were introduced.
The declaration docstring gives all five node proof steps, including descent of
faithful flatness by complexes and the explicit tensor formula for the section.

Edge cases checked: the zero ring is permitted (there are no maximal ideals, so
only the final universal clause is vacuous); no characteristic is fixed; no
noetherian or local-ring assumptions are inserted. The identity algebra is among
the tested algebras and has its identity section. The zero algebra over a nonzero
base is not faithfully flat, so it is not erroneously required to have a section.
The construction includes the empty finite tensor and stage zero; the theorem
uses their existing definitions and makes no new choices of representatives.
Universes and all variables are explicit; no local notation, local instance,
private definition, or let binder occurs in the statement.

Searches for an exact existing statement:

- msearch.py leanfinder, query “Etale contraction is faithfully flat ind etale and
  etale covers split with strictly henselian maximal localizations”: eight hits
  on Etale composition, localization, and ring/algebra equivalences; none for
  this construction's properties.
- msearch.py loogle, query “Algebra.IndEtale, Module.FaithfullyFlat”: zero hits,
  unknown identifier Algebra.IndEtale (it is a project notion).
- msearch.py leansearch, query “Etale contraction faithfully flat ind etale
  strictly henselian maximal localizations”: unavailable, Internal Server Error.
- msearch.py grep, query `etaleContraction|EtaleContraction|contraction.*henselian`:
  zero Mathlib hits.
- rg on WeilConjectures and lean/Sheaf for
  `etaleContraction|EtaleContraction|lem-weil-pbc-etale-contraction`: the side
  construction exists with no property theorem. The upstream properties in
  ProEtaleContraction and RetractionsStrictlyHenselian concern IndEtaleContraction,
  a different construction. They cannot be attached for this node. Read the
  upstream strictly henselian retraction criterion's full signature and docstring.
- rg for `etaleContraction_properties` on the upstream name index, both project
  sources and Mathlib: no collisions.

Source checked: the complete blueprint lemma at order 1227 and Stacks proetale.tex,
construction preceding lemma-first-construction and that lemma's proof. The Lean
uses exactly the recorded construction and all clauses of the unit statement.

Validation: scompile.py compiled the delivered module cleanly on the server
(nice 19, two threads, 60 seconds per file), including its required side overlays.
No local compiler or library build was run. Delivery dry-run result is recorded
by the tool output; no push is made by this worker.


## Second reading by NA

Independently read the node, its seven statement-dependency records, their actual
source declarations, the full delivered module, blueprint order 1227, and Stacks
proetale.tex section Constructing ind-etale algebras, the construction preceding
lemma-first-construction, that lemma and its proof, and Tag 097V
lemma-have-sections-strictly-henselian. The source begins with an arbitrary ring;
there is no standing noetherian, nonzero, local, characteristic, or field assumption.

Object/hypothesis/conclusion checklist, in the node's order:

- Arbitrary commutative R: `(R : CommRingCat.{u})`. PASS: precisely a bundled
  commutative ring, no further instance on R.
- Its specified R-e and structural map: `R.etaleContraction` and
  `(EtaleContraction.ι R 0).hom`. PASS: opened Representatives, finiteDiagram,
  step, stage, sequence, etaleContraction and ι in the dependency module.
  Representatives uses Skeleton of the small model of faithfully flat etale
  algebras; the finite-family diagram includes the empty family; the sequential
  limit is in opposite commutative rings. Stage zero reduces to the given ring.
  Thus the map is the canonical R-to-R-e map, not an arbitrary algebra action.
- Faithful flatness of that map: its `.FaithfullyFlat`, first conjunct. PASS:
  opened RingHom.FaithfullyFlat, which installs exactly the map's toAlgebra and
  uses Module.FaithfullyFlat. The latter is the recorded Mathlib class, flatness
  with proper maximal-ideal extensions, equivalent to the node's exactness test.
- Ind-etaleness of the same map: its `.IndEtale`, second conjunct. PASS:
  opened RingHom.IndEtale and Algebra.IndEtale in ProEtale/IndEtale. The former
  installs the canonical map's toAlgebra; the latter is a filtered colimit
  presentation by Algebra.Etale algebras. Etale includes finite presentation.
  IndPrincipalZariski publicly imports this exact recorded notion.
- Every R-e algebra B: `∀ (B : Type u) [CommRing B]
  [Algebra R.etaleContraction B]`. PASS: every commutative algebra in the fixed
  universe of the construction, with its structure map quantified before its
  properties. No finite dimensionality, nontriviality, or other restriction.
- Faithfully flat, etale, finitely presented hypotheses on B: the three arrows
  `Module.FaithfullyFlat`, `Algebra.Etale`, `Algebra.FinitePresentation`, all
  over R.etaleContraction. PASS: opened the Mathlib definitions, including
  FinitePresentation's surjective polynomial presentation with finitely generated
  kernel. Opened AlgebraicGeometry.Etale's HasRingHomProperty instance: this is
  precisely the affine ring version of the recorded scheme notion. Explicit
  finite presentation repeats a consequence of etaleness without strengthening it.
- Existence of a section: `Nonempty (B →ₐ[R.etaleContraction]
  R.etaleContraction)`. PASS: an algebra hom into the identity base algebra
  commutes with the structure map, hence its composite with that map is identity.
  Conversely every ring-map retraction is such an algebra hom. This states
  existence only, neither a chosen nor a unique section.
- Every maximal localization strictly henselian: `∀ (m : Ideal
  R.etaleContraction) [m.IsMaximal], IsStrictlyHenselianLocalRing
  (Localization.AtPrime m)`. PASS: opened Localization.AtPrime (localization at
  the prime complement) and the upstream strictly henselian class (extends
  HenselianLocalRing and asserts separably closed residue field). Maximality
  supplies primality; no arbitrary-prime strengthening is made.

Edge cases: PASS. The zero ring/empty spectrum is included: an algebra over the
zero ring is itself subsingleton, so the section clause remains meaningful; the
maximal-ideal clause has no instances. For nonzero base the zero algebra fails
faithful flatness. Identity algebras qualify and admit identity retractions.
No characteristic is restricted. Empty finite tensors and stage n = 0 are
included by the dependency, and no nonempty index assumption was added. The
universe u is explicit and shared with the fixed-universe construction and the
recorded IndEtale predicate; there is no independent smaller test universe.
Moreover finite presentation bounds the size of every tested algebra by the
base plus finitely many generators, so larger-universe finitely presented
algebras have representatives at this size. There are no free universes or
variables, local notation, private objects, or local instances in the delivery.

Independent searches used different wording from the worker:

- msearch leanfinder: "A sequential tensor construction splits every faithfully
  flat etale cover and has separably closed henselian local rings". Eight hits,
  including Algebra.Etale.exists_subalgebra_fg, baseChange, and the field product
  characterization; none states the properties of this contraction.
- msearch loogle: `Algebra.Etale, Nonempty (_ →ₐ[_] _)`: zero hits.
- rg across Mathlib, upstream WeilConjectures, project lean/Sheaf, and the upstream
  declaration-name index for etaleContraction, IndEtaleContraction,
  forall_retraction, and contraction with faithful flatness. No exact existing
  theorem on CommRingCat.etaleContraction or name collision. Opened the upstream
  ProEtaleContraction definition and property signatures and the final generic
  retraction criterion in RetractionsStrictlyHenselian. IndEtaleContraction uses
  the non-skeletal SmallModel rather than the recorded skeleton construction;
  its property statements therefore do not attach to this object. The generic
  maximal-local criterion is already reused as a proof import, not restated.

No mismatches found; no Lean, node statement, or dependency changes were needed.
There are no new nodes or dependency modules to audit. No hollow definition or
extra proved lemma occurs: the sole theorem has exactly `by sorry`. Its source
and blueprint docstrings are present and the proof plan follows all five node
proof steps (finite tensors, colimits, descent including faithful flatness,
explicit tensor retraction, maximal-local criterion). Stated proof-dependency
imports are present; the unrecorded directed-colimit node remains listed by the
worker as unavailable for import, with no substitute statement introduced.
Verified the node's lean.statement verbatim against the file signature.

Validation: independent scompile.py invocation passed on the server: the delivered
module took 1.5 seconds; required side overlays also compiled cleanly. Every
invocation used nice 19, two threads, and the 60-second per-file limit. No local
compiler, lake build, or live-library write was used. Only this review report was
changed by the second reader.
