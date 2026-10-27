## Worker report

Stage 2 assignment, Q112, 2026-10-23. The inherited BLOCKED ending concerns
stage-1 preflight, not this assignment: coord/queue.tsv lists this item at stage 2,
the accepted stage-1 split has no lean record, and coord/brief-stage2.md §0
explicitly directs this handoff to deliver2.py. The preserved sandbox was empty.
No stage-1 statement, proof, source, review, or other accepted field is changed.

The item states AddMonoidAlgebra.exists_formalMonoid_implicitElimination in
Sheaf.RingTheory.FormalMonoidImplicitElimination. This exact theorem is recorded
on lem-per-formal-monoid-implicit-elimination, but its module was deleted on
2026-10-20. Both the local sources and scompile.py --source confirm the module
is absent. This delivery restores its previously reviewed signature and the
complete ten-step natural-language proof, with a single sorry proof, owned by
this item's lean.file. There is one theorem declaration and no new definition.
Only the item's lean field changes; its statement dependencies stay unchanged.
The old proof dependency's record is not re-bound or changed.

Hypotheses and objects, clause by clause (the same mapping applies to both nodes):

- D is a commutative ring: (D : Type u) [CommRing D]. Noetherian:
  [IsNoetherianRing D]. Local and nonzero: [IsLocalRing D], which extends
  Nontrivial D in Mathlib/RingTheory/LocalRing/Defs.lean. Complete:
  [IsAdicComplete (IsLocalRing.maximalIdeal D) D], including separatedness.
- S and T are additive commutative monoids in independent universes v and w.
  hS and hT use AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative _).
  This is precisely finite generation, injectivity into the canonical group
  completion, and saturation; no torsion-free or freeness hypothesis is added.
- hsharpS and hsharpT say every unit is zero. Zero is already a unit, so this
  is exactly the sharpness condition. Multiplicative is only a change of notation.
- β : S →+ T is the homomorphism; hβ says β s = 0 implies s = 0. The converse
  follows from map_zero, so the zero fibre is exactly {0}.
- D[P] is Mathlib AddMonoidAlgebra D P, with monomials single p d. aS, aT,
  aH and their equalities haS, haT, haH name exactly the coefficient maximal
  ideal plus the ideal spanned by nonzero monomials. Quantifying those ideals
  with their defining equalities does not restrict or enlarge the instances.
- AdicCompletion aP (AddMonoidAlgebra D P) is D[[P]] as the inverse limit of
  the quotient rings. S ⊕ T is S × T with componentwise addition. The topology
  is ⨅ n, TopologicalSpace.induced (AdicCompletion.evalₐ aP n) ⊥: the inverse
  limit topology of discrete quotient rings, not the discrete topology on D[[P]].
- u : Multiplicative S →* (AdicCompletion aS (AddMonoidAlgebra D S))ˣ is
  precisely the arbitrary unit-valued homomorphism in the node.

Conclusions, clause by clause:

- The continuous ring homomorphism ι is the coefficient-and-S-monomial inclusion
  into H: its value on every single s d is prescribed as single (s,0) d.
  This is the canonical map, characterized on the dense monoid algebra into the
  separated completion; it is not an arbitrary extra input.
- I is existentially named with the equality to Ideal.span of exactly
  X^s - ι(u(s)) * Y^(β s), including s = 0. That generator is zero at s = 0.
- e is a ring equivalence from D[[T]] to H/I. Its displayed value on every
  monomial single t d prescribes the coefficient-and-Y-monomial map.
  Continuity of e and e.symm is explicit, with the quotient topology on H/I
  written using TopologicalSpace.coinduced (Ideal.Quotient.mk I).
- For every nonzero s, e.symm of the class of X^s belongs to the algebraic
  Ideal.span of nonzero Y-monomials. This is the actual generated ideal,
  not only its closure or the maximal ideal.
- ε is the continuous augmentation D[[T]] → D (D has its maximal-ideal-adic
  topology), prescribed on single t d by if t = 0 then d else 0.
  The last equality says ε (e.symm (class of the coefficient d)) = d for all d.
  Thus the inverse induces exactly the identity on the coefficient stratum.
- The final two explanatory sentences in the item's statement are rendered by
  IsLocalRing, IsAdicComplete and the product monoid; they add no conclusion.

Dependency declarations read and used:

- def-weil-pbc-noetherian-ring: Mathlib.RingTheory.Noetherian.Defs,
  IsNoetherianRing (all ideals finitely generated).
- def-weil-pbc-adic-completion: Mathlib.RingTheory.AdicCompletion.Basic,
  AdicCompletion, AdicCompletion.of, IsAdicComplete; Algebra supplies the
  ring structure and AdicCompletion.evalₐ.
- def-trf-fs-log-blowup: Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup,
  importing Sheaf.AlgebraicGeometry.LogRegularPair and its
  AlgebraicGeometry.IsFineSaturatedMonoid. The log scheme/blowup objects
  are not additional hypotheses: only the fs monoid notion is used here.
- lem-per-formal-monoid-implicit-elimination: the identical formerly recorded
  theorem. Its module was deleted, and restoring that module would make an
  import of this proof dependency a self-import. Omit that import to avoid the
  cycle. The full ten-step proof behind that exact reuse is in the docstring.
  Its available underlying proof dependencies are imported
  as plain imports: AdicCompletion.LocalRing, FiniteType,
  WeilConjectures.RingTheory.AdicCompletionNoetherian, and
  WeilConjectures.RingTheory.CompleteLocalQuotient. Its evaluation proof
  dependency has a deleted module, so its import is omitted and its use is
  fully documented in the proof plan. No proof is attempted at stage 2.

Edge cases checked mathematically before writing: S = {0} gives the identity
on D[[T]], with a zero relation ideal and vacuous inverse-X clause. T = {0}
forces S = {0} by hβ, giving D and its identity augmentation. For a field D the
coefficient maximal ideal is zero; the monomial-adic completion and augmentation
still have the same meaning. Nonreduced complete Noetherian local D is allowed;
no domain hypothesis occurs. For S = T = ℕ, β(1) = m > 0 and u(1) = 1 + X,
the solution X = Y^m/(1-Y^m) lies in (Y), and reduces to zero on the stratum.
If the zero-fibre hypothesis were omitted, β(1) = 0 and u(1) = 1 would impose
X = 1 and collapse the local formal quotient; the hypothesis is essential.
No coefficient characteristic is excluded. Universes u, v, w are explicit and
independent; autoImplicit is disabled. The theorem has no unbound variables.

Searches made for existing declarations:

- msearch.py leanfinder: "A complete sharp fine saturated monoid algebra modulo
  unit twisted implicit monomial equations is continuously isomorphic to the
  target monoid algebra": 8 hits, ordinary MonoidAlgebra congruences/lifts,
  no implicit-elimination theorem.
- msearch.py loogle: "AdicCompletion, MvPowerSeries.eval₂": 0 hits.
- msearch.py grep, RingTheory: "implicitElimination|implicit.*[Mm]onoid|[Mm]onoid.*implicit":
  0 hits.
- msearch.py leansearch: "Implicit unit twisted equations in complete sharp fine
  saturated monoid rings yield a continuous isomorphism fixing the coefficient
  stratum": 8 hits, continuous monoid equivalences and localization/unit facts,
  no exact theorem.
- rg over lean/WeilConjectures and lean/Sheaf for IsFineSaturatedMonoid,
  exists_formalMonoid_implicitElimination, formalMonoid.*[Ii]mplicit,
  implicitElimination, and the item id: the fs definition and related completed
  chart/dimension modules exist; the implicit-elimination declaration does not.
- DAG inspection finds the exact earlier theorem and its reviewed Lean record,
  whose signature is restored on this item. No new notion is needed.

Source read: ILO PDF pages 78–79, printed pp. 72–73, Exposé VI 2.3, obtained
with pdftotext. It gives the completed sharp monoid Kummer charts and the
coefficient-stratum identity. The arbitrary unit-twisted elimination is correctly
identified in both source records as an agent-formulated algebraic refinement,
not a verbatim theorem of ILO. There is no statement correction or dispute.

Validation: scompile.py compiled the restored module in sandbox mode (8.5 s)
and library mode (7.4 s), both clean, after repairing one missing adic-topology
import and replacing open scoped Classical by declaration-scoped open Classical in.

Preflight repair: the first packet attempted existing: true reuse of a module
restored in the same delivery. The server requires an existing module to be
present in published sources, so it refused that record. The final packet instead
attaches the module to this item with existing: false, leaves stmt_deps unchanged,
and removes the unnecessary dependency node edit. This resolves the refusal
without introducing a second statement or a theorem statement-dependency edge.

## Second reading by Q112

A separate reading pass by the same worker (the current dispatcher explicitly
forbids starting other agents); independent review is left to the maintainer.
Read the item and the matching earlier node, the dependency records and sources, and the
restored Lean signature. Matched D's nonzero/local/complete/Noetherian conditions,
sharp fs S,T, the zero fibre of β, arbitrary unit twists, all three completion
ideals, the canonical inclusion ι, relation ideal I, continuous equivalence e
and continuous inverse, the algebraic inverse-monomial ideal clause, and the
coefficient augmentation identity. All match. The dependency statement is the
item statement word for word except for its final explanatory sentences. No
mathematical mismatch was found; only the compiler import/scope fixes and module ownership/preflight repair described
above were made. No independent second reader is claimed.
