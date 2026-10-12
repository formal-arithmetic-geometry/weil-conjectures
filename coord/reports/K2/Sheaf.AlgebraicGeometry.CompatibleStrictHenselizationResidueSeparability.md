## What changed

Added a `STATEMENT-DISPUTED` comment immediately before
`AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_isSeparable` in
`Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueSeparability`.
Its signature, docstring, proof, visibility, and imports are unchanged. The statement is
false for the arbitrary Algebra instance it quantifies over, so no purported proof or
reduction of it is supplied. This is the disputed-statement delivery allowed by
AGENTS.md §5 and coord/brief-stage3.md §4, not an abandonment for lack of a proof.

## Proved and sorry left

Closed: none (0 of 1). Added: none. Split off: none.
The existing hole remains in
`AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_isSeparable`, node
`lem-weil-pbc-compatible-strict-henselization-residue-separability`.
The scratch counterexample below compiled through lcompile.py without sorry; its
`#print axioms` contains only propext, Classical.choice, and Quot.sound. It is evidence
for the dispute, not a new library declaration or a claim that the full geometric
counterexample has been formalized. No Lean target is changed.

## No longer needed

None. No imports, nodes, or modules are pruned: the intended geometric argument still
needs a correctly specified residue separability theorem. The unit sk-thm-p1 and all
of its realized statement and proof steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: `[Algebra (IsLocalRing.ResidueField B) k']` is unrelated to ρB.
`IsSeparable (IsLocalRing.ResidueField B) y` is relative to its implicit algebraMap.
Neither hι nor hρA nor hρB mentions that algebraMap. They constrain only the geometric
ring homomorphism `(Spec.preimage ρB).hom`. The proof plan's final transportation
step therefore cannot identify the algebra structure used in the conclusion.

Here is a counterexample meeting every geometric hypothesis, with residue fields
identified canonically with the fields themselves. Put F = an algebraic closure of
ℚ(u), put L = an algebraic closure of F(t), and let b : F → L be the canonical inclusion.
The variable t is transcendental over b(F). The embedding ℚ(u) → L sending u to t
extends to a field embedding a : F → L, because F is algebraic over ℚ(u) and L is
algebraically closed. Thus a(u) = t, which is not separable over F through b.

Take S = T = Spec F, g = identity, A = B = F, k = k' = Ω = L,
ι = ν = identity, and σ = τ = Spec.map a. Both F and L are algebraically closed,
so all separable-closedness assumptions hold, and fields are henselian local rings.
The strict henselization of the local ring F at the L-valued point a is F itself:
its residue separable closure over F is F, and an algebraically closed field is already
strictly henselian. Choose eA = eB to be the inverse of the canonical structural
isomorphism, so eA.hom followed by the structural map is identity (likewise for eB).
Choose ρA = ρB to be induced by a after the canonical residue identification
κ(F) ≅ F. Composing with the closed-point inclusion and the structural isomorphism
then gives σ = τ, so hρA and hρB hold. Since ι and g are identities, hι holds too.
Give L its κ(B)-algebra structure through b, rather than a, transporting along
κ(F) ≅ F. For x equal to the residue of u, the conclusion is IsSeparable F t under b,
contradicted by the transcendence of t. The mismatch persists even with both model
residue fields and both geometric-point fields algebraically closed.

Read the stated dependency signatures in Scheme.etale_local_ring_triples and
Scheme.strictHenselization_triples, and the already assembled
AlgebraicGeometry.strictHenselizationResidue. All their separability conclusions are
relative to specified base embeddings; none eliminates an arbitrary algebra-map mismatch.
The shorter-route searches were run with msearch.py: leanfinder (relative separable
closure and compatible base extension; 8 lower-level hits), loogle (IsSeparable,
algebraMap; no usable result), and grep (IsSeparable map/tower and strictHenselizationResidue;
25 lower-level hits). Mathlib's IsSeparable.map requires an AlgHom, and tower_top
requires IsScalarTower: both demand precisely the missing compatibility.

The local literature/stacks-project/etale-cohomology.tex file is absent on this
machine. Read the primary sources online instead:
[Stacks Tag 04HX](https://stacks.math.columbia.edu/tag/04HX) identifies the residue
field using the geometric base embedding; [Stacks Tag 095T](https://stacks.math.columbia.edu/tag/095T)
uses the inclusion of the two compatible separable residue closures. These sources
support the intended geometric statement, not quantification over an unrelated Algebra.

The sole direct user of the disputed declaration is
`Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial`.
It already installs `(Spec.preimage ρB).hom.toAlgebra` before calling the theorem.
The likely interface repair is to replace the arbitrary instance in the disputed theorem
with that locally specified algebra structure, or explicitly require
`algebraMap (IsLocalRing.ResidueField B) k' = (Spec.preimage ρB).hom`.
That is a statement correction requiring the project change-record and downstream
checks; it is not made silently in this delivery. The polynomial theorem's explicit-map
conclusion and the higher residue-image theorem are not refuted by this counterexample.

For reproducibility, this is the algebraic certificate compiled in the sandbox
scratchpad (Mathlib only). It constructs a and b and proves the failure of separability;
the paragraph above supplies the geometric specialization:

```lean
module
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.Separable
@[expose] public section
set_option autoImplicit false
noncomputable section

abbrev F := AlgebraicClosure (RatFunc ℚ)
abbrev L := AlgebraicClosure (RatFunc F)

def t : L := algebraMap (RatFunc F) L RatFunc.X

theorem t_transcendental : Transcendental F t := by
  exact (transcendental_algebraMap_iff (RingHom.injective _)).2
    (RatFunc.transcendental_X (K := F))

theorem t_not_separable : ¬ IsSeparable F t := by
  intro h
  exact t_transcendental h.isIntegral.isAlgebraic


def rationalEmbedding : RatFunc ℚ →+* L :=
  (IntermediateField.adjoin ℚ {t}).val.toRingHom.comp
    (RatFunc.algEquivOfTranscendental t
      (t_transcendental.restrictScalars (RingHom.injective _))).toRingHom

theorem rationalEmbedding_X : rationalEmbedding RatFunc.X = t := by
  exact RatFunc.algEquivOfTranscendental_X (K := ℚ) t
    (t_transcendental.restrictScalars (RingHom.injective _))

def otherEmbedding : F →+* L := by
  let : Algebra (RatFunc ℚ) L := rationalEmbedding.toAlgebra
  exact (IsAlgClosed.lift (R := RatFunc ℚ) (S := F) (M := L)).toRingHom

theorem otherEmbedding_X :
    otherEmbedding (algebraMap (RatFunc ℚ) F RatFunc.X) = t := by
  change (let _ : Algebra (RatFunc ℚ) L := rationalEmbedding.toAlgebra
    (IsAlgClosed.lift (R := RatFunc ℚ) (S := F) (M := L))
      (algebraMap (RatFunc ℚ) F RatFunc.X)) = t
  let : Algebra (RatFunc ℚ) L := rationalEmbedding.toAlgebra
  rw [AlgHom.commutes]
  exact rationalEmbedding_X

theorem two_embeddings_counterexample :
    ∃ x : F, ¬ IsSeparable F (otherEmbedding x) := by
  refine ⟨algebraMap (RatFunc ℚ) F RatFunc.X, ?_⟩
  rw [otherEmbedding_X]
  exact t_not_separable

#print axioms two_embeddings_counterexample
```

## Second reading by K2

1. I compared the delivered module against the repository version. The only change is the
`STATEMENT-DISPUTED` comment; imports, declaration signature, visibility, and proof are
unchanged byte for byte.

2. The module and the algebraic counterexample scratch file compile with `lcompile.py`.
The remaining theorem has its original named `sorry`; no definition contains `sorry`, and
the scratch counterexample uses only the permitted axioms.

3. The disputed statement is false as written because its arbitrary `Algebra` instance is
not tied to `(Spec.preimage ρB).hom`; the counterexample in this report establishes the
mismatch. No split-off statement was added, and no duplicate library result was introduced.

4. The proof route and imports remain unchanged because the geometric argument cannot prove
the statement with the current interface. The unit `sk-thm-p1` route and realized nodes are
preserved.

5. The DAG node still matches the unchanged Lean declaration and proof dependencies. No
pruning is possible until the interface is corrected by a project-level change record.

I changed only the declaration comment and this second-reading report section. The proper
repair is to require the algebra structure to be induced by `(Spec.preimage ρB).hom` (or an
equivalent compatibility equality), which is outside this proof-only delivery.
