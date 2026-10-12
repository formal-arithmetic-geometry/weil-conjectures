## What changed

Replaced the proof hole in
`AlgebraicGeometry.IsCurve.exists_constantModSheaf_one_frobenius_baseChange_model`
with a complete Lean composition proof. The existing signature, visibility and docstring
are unchanged. Added two proof-only imports:
`Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPrimeBaseChangeModel` and
`Sheaf.AlgebraicGeometry.Curve.ConstantModCohomologyFinsuppPullback`.

The first new statement handles the prime-field Artin--Schreier kernel and coherent
base-change comparison, without arbitrary coefficients or an indexing type. The second
handles coefficient direct sums and naturality for any morphism between qcqs schemes,
any coefficient ring and any nonnegative cohomological degree; it has no Frobenius,
field-extension, curve, connectedness, smoothness or properness hypotheses.

The composition establishes qcqs instances using quasi-compactness/separatedness of
the curve and properness after pullback. It composes the coordinate equivalences with
`Finsupp.mapRange.addEquiv` of the prime-coefficient equivalences. Evaluation at each
coordinate, the coefficient naturality equation and the prime-coefficient equation
then prove exactly the original compatibility statement.

Compiled all three modules in import order through lcompile.py. No compiler warnings.
Read the proofs in Stacks [0A3P](https://stacks.math.columbia.edu/tag/0A3P),
[02KH](https://stacks.math.columbia.edu/tag/02KH),
[03Q5](https://stacks.math.columbia.edu/tag/03Q5) and
[0739](https://stacks.math.columbia.edu/tag/0739).

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.IsCurve.exists_constantModSheaf_one_frobenius_baseChange_model`
(node `lem-sc-artin-schreier-base-change-model`). No sorry remains in the assigned module.

Added two strictly separate argument obligations:

- `AlgebraicGeometry.IsCurve.exists_constantZMod_one_frobenius_baseChange_model`,
  node `lem-pbc-artin-schreier-prime-base-change-model`, in
  `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPrimeBaseChangeModel`.
- `AlgebraicGeometry.Etale.exists_constantModSheaf_cohomology_finsupp_pullback`,
  node `lem-pbc-constant-mod-cohomology-finsupp-pullback`, in
  `Sheaf.AlgebraicGeometry.Curve.ConstantModCohomologyFinsuppPullback`.

Each is a public named theorem with its complete proof in words and source; its entire
proof is `:= by sorry`. This delivery is a decomposition: one upper hole closed, two
lower holes added, net -1. It is not an unconditional proof of the original theorem.
No definition, axiom, private hole or arbitrary witness construction was added.

## No longer needed

None. No original import was removed; all are public imports belonging to the existing
statement interface. The original seven proof-dependency nodes remain needed by the
new obligations: the five Artin--Schreier/coherent comparison dependencies belong to
the prime model; finite-sum presentation and large filtered-colimit continuity belong
to the coefficient comparison. They are replaced in the parent's direct proof_deps
by the two new nodes, rather than pruned. No existing module or unit step is bypassed.
The fixed-point invariance argument stays in the parent ProperConstantBaseChangeOne.

## Where the brief, the DAG or earlier work was wrong

The scalar-model and proper-degree-zero lemmas in the original plan require
`IsConnectedCurve`, which includes dimension exactly one. The assigned statement
assumes `IsCurve` and `ConnectedSpace`, allowing dimension zero. The prime-model
obligation explicitly includes the dimension-zero case: a smooth proper connected
zero-dimensional scheme over an algebraically closed field is Spec k; coherent H¹
and both Artin--Schreier H¹ groups are zero. The original statement is unchanged.

The finite-sum colimit theorem supplies a colimit diagram and separate finite-stage
isomorphisms, but its signature does not retain a chosen basis or compatibility of
those isomorphisms with transitions. It suffices for vanishing arguments, but cannot
alone recover the natural Finsupp coordinates required here. The new coefficient
obligation retains that compatibility by repeating the explicit basis construction
from that theorem's proof and tracking all summand inclusions. Its source, docstring
and node record state this requirement rather than assuming it follows from the
bare existential presentation. No existing statement is disputed or changed.

## New nodes

`lem-pbc-artin-schreier-prime-base-change-model` isolates original proof steps 1--2:
prime-coefficient kernel identification, finite-dimensional Frobenius and flat coherent
base change, including naturality. Its statement is independent of Λ and I. The node
records the five corresponding existing proof dependencies and the dimension-zero
case. Edge cases: zero coherent H¹ gives the zero vector space; no kernel invariance
or bijective comparison is assumed.

`lem-pbc-constant-mod-cohomology-finsupp-pullback` isolates original proof step 3:
coefficient-basis direct sums, qcqs cohomology continuity and pullback naturality. Its
statement works in every degree on arbitrary qcqs schemes and does not use the first
new node. Edge cases: Λ/(p)=0 gives an empty basis; infinite bases give genuinely
finitely supported sums; empty schemes have zero cohomology. The original proof
steps and the binding unit route are retained through these two nodes.

No interface changes or forced adaptations; no change record is needed.

## Second reading by F1

1. **Unchanged interface: PASS.** Compared the assigned module with the repository
   using diff. The sole existing declaration's signature and docstring are byte for
   byte unchanged. The only differences are two plain proof-only imports and the
   replacement proof body. The two other modules are new; there are no definitions,
   interface changes, change records, or forced adaptations.
2. **Kernel-checked composition: PASS, conditional decomposition.** Compiled all three
   delivered modules in import order with lcompile.py, without errors or unexpected
   warnings. Inspected all their code: the only holes are the two reported public
   named theorem bodies, each exactly `:= by sorry`. There is no axiom, unsafe,
   opaque, implemented_by, extern, hollow definition, or witness-chosen definition.
   A scratch copy with #print axioms for all three declarations shows only propext,
   Classical.choice, Quot.sound and sorryAx. Thus the original hole is closed by a
   valid composition, but the result still depends on the two open obligations.
3. **Split statements: PASS.** Read both statements, their complete docstring
   arguments, their nodes, and the declarations of all seven old dependencies.
   Independently checked Stacks 0A3P, 02KH, 03Q5 and 0739. Prime-field comparison
   follows Artin--Schreier exactness, coherent finiteness and flat base change;
   coefficient comparison follows a fixed coefficient basis, finite subcoproducts,
   continuity and naturality. The prime statement omits arbitrary coefficients;
   the coefficient statement omits every Frobenius and curve-model conclusion, so
   neither merely renames the original argument. Checked Spec k (V = 0), zero
   quotient (empty basis), empty schemes for the coefficient statement, infinite
   bases, degree zero and identity pullback. The prime statement's ConnectedSpace
   hypothesis excludes empty schemes. Ran independent leanfinder searches using
   H1/kernel/pth-power and qcqs/direct-sum terminology, a loogle search for the
   already-used Finsupp equivalence, Mathlib grep and repository rg. No existing
   declaration closes either geometric/naturality obligation in a few minutes.
4. **Route and pruning: PASS.** Read sk-thm-p1.json, including its realized statement
   and four steps. The delivery splits below that unit and retains its characteristic-p
   Artin--Schreier route. The five old prime-model dependencies and two old
   coefficient dependencies are retained in the new nodes' plans; no old dependency
   is abandoned. Both added imports are proof-only and used. The retained public
   imports provide the existing statement's vocabulary. There is no shorter
   available complete theorem identified by the independent searches, and no
   module is claimed as pruned.
5. **DAG correspondence: PASS.** The parent's proof and its two direct proof_deps
   describe the actual qcqs setup, two applications, Finsupp equivalence composition
   and coordinate rewrite. Its only changed fields are proof, proof_deps and
   proof_origin. Each new node has its statement dependencies, source, proof steps,
   dependency union, origin, searches, split status, creation record, blueprint
   provenance, chapter/unit and matching Lean declaration record. The two new
   signatures agree with their nodes and the original statement is unchanged.

Second reading changed only this report, adding the independent review and explicit
axiom evidence; no Lean or DAG repair was required. This remains one original hole
closed and two strictly lower holes added (net -1), not an unconditional proof.
