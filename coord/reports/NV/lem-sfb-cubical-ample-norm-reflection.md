# Stage 1 delivery: lem-sfb-cubical-ample-norm-reflection

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cubical-ample-norm-reflection.json: item split, original statement retained; seven actual Mathlib queries recorded.
- dag/nodes/sec-six-functors-basics/lem-sfb-cubical-antisymmetric-frame-extension.json: new statement-only geometric construction, unsplit, no Mathlib match (six actual searches).
- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-gm-extension-ample-reflection.json: new statement-only group-quotient ampleness input, unsplit, no Mathlib match (six actual searches).
- citations.json: one verbatim statement quotation for every step/use pair.

There are two new statement nodes and zero Mathlib leaves. Neither new node claims a finished proof. The assembly proof has five steps, 2153 characters in total; no step exceeds 2000 characters.

## Attachments

None. I searched the live project WeilConjectures directory for the item tag and for cubical, cubist, semiabelian, ample/norm and quotient terminology. No project declaration gives this assertion without sorry. Mathlib searches returned affine scheme pullbacks, category group objects, ring Picard groups and topological bundles, not either required geometric theorem. The ring Picard tensor/dual identities are local linear algebra, not a specialization establishing a group structure on a scheme or a relative ampleness comparison.

## Sources and WANTED

WANTED: Michel Raynaud, Faisceaux amples sur les schemas en groupes et les espaces homogenes, LNM 119 (1970), Chapters IV and XI, especially XI 1.11, for lem-sfb-cubical-ample-norm-reflection and lem-sfb-semiabelian-gm-extension-ample-reflection. The exact relative Gm-extension formulation needs an independent proof; it is explicitly agent-formulated, not attributed verbatim to XI 1.11. The original is absent from local literature. The publisher chapter landing page was accessible, but its content was subscription-only: https://link.springer.com/chapter/10.1007/BFb0059517 .

WANTED: Laurent Moret-Bailly, Pinceaux de varietes abeliennes, Asterisque 129 (1985), Chapter I, cubical torsors, second differences and extensions (I 2 and I 5), for lem-sfb-cubical-antisymmetric-frame-extension. The local text is absent. The online original https://numdam.org/item/AST_1985__129__1_0.pdf was rejected by the browser as too large (22,585,214 bytes). Its bibliographic landing page was read. This new node is an agent-formulated construction, not an invented numbered quotation.

I read Ning Guo, Divisors on Coherent Schemes and Homogeneous Spaces, March 31 2026, Sections 5.5 and 6, especially Corollaries 6.5 and 6.6, at https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf . These give the group-action ampleness context but are not asserted to state Gm-extension reflection. I read Lan's revised thesis, Chapter 3.3 and Lemma 4.2.1.6 / 4.2.1.8 context, at https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision-dense.pdf . Its abelian-quotient comparison is related evidence, not a proof of the more general relative assertion. No SGA source is used.

## Errors and choices

The target was unsplit, with no released repair order. Its statement is retained. Its source already calls it an agent-formulated input and distinguishes its global norm assumption from fibrewise positivity. I found no counterexample to that statement.

A tempting use of lem-sfb-cubical-fibrewise-ample-criterion would be circular: it uses lem-sfb-cubical-strict-local-affine-seed, whose step 8 is the present item. The supplied-norm-ampleness and generic-extension parents also lead through that chain. None is used here.

A second tempting proof uses the cubical multiplication recurrence followed by finite-flat ample reflection. Relative multiplication on a semiabelian family need not be finite when toric rank jumps (e.g. a semistable elliptic degeneration). Thus the existing field-only lem-sfb-semiabelian-invertible-multiplication is insufficient. I did not generalize it silently.

Instead, the quotient is the actual antisymmetric frame extension, with positive-dimensional connected kernel Gm. The geometric reflection input is stated separately. Its scope is group quotients, not arbitrary torsors and not a fibrewise ampleness criterion. The elementary factor cancellation connecting this geometry to the supplied inversion norm remains in the item.

## Not duplicates

lem-sfb-cubical-antisymmetric-frame-extension vs lem-sfb-semiabelian-picard-multiplicative-torsor: the existing node assumes geometric algebraic triviality of a supplied line over a field; the new one constructs the antisymmetric line from supplied cubical data over the normal affine base and includes the coherent group structure on its actual frame scheme. No fieldwise-to-relative implication is taken from the existing node.

lem-sfb-cubical-antisymmetric-frame-extension vs lem-sfb-semiabelian-second-difference-diagonal: the existing statement is over a field and constructs a biextension plus a geometric algebraic-equivalence class; it does not give the relative antisymmetric frame extension with its group and torsor structure.

lem-sfb-cubical-antisymmetric-frame-extension vs def-sfb-cubical-rigidified-line: the latter is input data and coherence axioms, not the theorem constructing an antisymmetric extension with the required geometry.

lem-sfb-semiabelian-gm-extension-ample-reflection vs lem-sfb-semiabelian-abelian-quotient-ample-reflection: the existing node is over a field and has proper abelian target; the new one has a normal affine base and a possibly nonproper semiabelian target, with specifically Gm kernel. The field theorem is not sufficient for the relative conclusion.

lem-sfb-semiabelian-gm-extension-ample-reflection vs lem-sfb-relatively-ample-subtorus-quotient-schematicity: the existing node proves that a quotient is a scheme and its map is affine; it makes no assertion about a specified line downstairs being ample. In the new input both schemes are already supplied.

lem-sfb-semiabelian-gm-extension-ample-reflection vs lem-sfb-space-relative-ampleness-fpqc-descent: that node descends relative ampleness along a cover of the BASE. Here q covers the total group, not the base. General fpqc descent of absolute ampleness would be false.

lem-sfb-semiabelian-gm-extension-ample-reflection vs lem-sfb-cubical-ample-norm-reflection: the new input concerns arbitrary supplied group extensions and arbitrary invertible modules, with no cube, inverse or norm. The item constructs a particular extension and compares two distinct pullbacks by a tautological cancellation; it is not an application to a relabelled inversion norm.

The DAG and the newest blueprint were searched by keywords including antisymmetric cubical, multiplicative torsor, torus quotient ampleness and Gm extension ampleness. No equivalent blueprint node was found; both same_as arrays are empty. The inherited nearest-blueprint-ancestor field is null, as returned by tools/blueprint_refs.py; the full inherited provenance and via chain are preserved and extended.

## Review by NV

I read coord/delivery-errors.md B through E and checked the present statements and steps against its failure modes. I read the original item, its chapter and unit, the newest blueprint direct-image proof (3), the affine-seed proof using it, the field algebraic-equivalence/norm split, the field second-difference statement, and all the five statements quoted in citations.json. The actual mathematical work left as new inputs is visible in their statements. I have not claimed that the unavailable originals were read, or that the group-quotient input has already been proved.

For the antisymmetric construction, the cube pulled back along (x,y,-x-y) has zero sum and pair sums x+y, -y, -x. After the rigidification at zero, its factor identity is L_x L_y L_{-x-y} = L_{x+y} L_{-y} L_{-x}. Rearranging gives D_x D_y = D_{x+y}. A bare Picard equality would not prove a group law: the new statement expressly requires the associative, commutative and unit equalities of the actual induced maps. It also requires the faithfully flat finite-presentation affine frame torsor, its scalar-kernel identification and semiabelian geometry. These are genuine construction/coherence content, not a one-line tensor lemma. The frame scheme is defined independently of the theorem, by local frames; no hollow choice or existence-only unspecified scheme is introduced.

Step 1 uses that new construction, whose hypotheses are literally those of the item. The quoted tautological trivialization and the rest of that statement give every property taken from it. Step 2 uses the full tensor-pullback compatibility clause of lem-weil-pbc-invertible-pullback-tensor. Evaluation of a line with its dual is written explicitly in a frame, so no hidden Picard or descent comparison is invoked. Its isomorphism is on all of E. Step 3 uses precisely the affine-pullback theorem: q is affine by step 1 and N is globally ample by hypothesis, so no improper arbitrary pullback assertion occurs. Step 4 uses exactly the implication stated in the new Gm-extension reflection input. Both groups have all of that input's hypotheses, q has the required kernel and group action, and the ample module upstairs is exactly q*(P squared). Step 5 quotes the ampleness definition and uses the same affine section loci of powers with exponent 2n. It needs no existence theorem or new ampleness lemma.

I tested the statements on S a field, the trivial group G=S, the split torus, the zero-dimensional abelian variety and products of a torus with an abelian variety. For the trivial group the rigidification makes D trivial, E=Gm and all lines on affine S are ample; all constructions and the conclusion agree. A trivial multiplicative twist gives E=G times Gm. On an abelian variety the antisymmetric line is in Pic^0 and the reflection reduces to the established algebraic-equivalence picture. No parity restriction or invertibility of 2 is used, so characteristic 2 is included. The toric rank may vary: the new statements do not assert finiteness of any multiplication map. The empty base is excluded by integral; rank-zero torus and dimension-zero fibres cause no step to fail.

I also tested the essential group hypothesis of the reflection input against a general Gm-torsor: the nonzero-vector torsor of O(-1) over projective space can be quasi-affine while O downstairs is not ample. It is not a group extension, so it is excluded. This is why a generic fpqc ampleness theorem is neither cited nor asserted. Source availability and the need to prove the explicitly relative quotient input remain accurately exposed, rather than hidden behind a source label.

I corrected the initially considered circular and finite-multiplication routes before writing the delivery. I kept the mathematical hypotheses unchanged, created no positivity clause duplicating the target, and left the two genuine inputs unsplit as required.

## Unfinished

Stage 1 splits the item completely by the two stated inputs. Their proofs, formal statements in Lean, all compilation and later stages are outside this delivery. The original texts listed WANTED are not downloaded or fabricated. There is no statement dispute and no claimed Lean attachment.
