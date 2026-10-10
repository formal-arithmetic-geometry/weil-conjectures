# Lead review: `lem-weil-pbc-torsion-extension-flat-descent`

## Review by K1

### Sources and statement agreement

I read More on Algebra, Lemma 05EG (`literature/stacks-project/more-algebra.tex`,
label `lemma-neighbourhood-extensions`, lines 24477--24556).  Its hypotheses are
exactly a flat map `R -> S`, a finitely generated ideal `I`, an isomorphism
`R/I -> S/IS`, an `I`-power-torsion source module, and an extension after scalar
extension.  The diagram in lines 24481--24500 is precisely the item conclusion,
including exactness and compatibility with both end maps.  The item makes the
same objects and maps explicit and does not add a hypothesis or weaken the
conclusion.  The item also records the derived 05EH formulation only as a
background source; its proof uses the module proof 05EG.

The read-only slopmaster2 checkout was searched before this review:

* `rg -n -F '(blueprint: lem-weil-pbc-torsion-extension-flat-descent)'`
  and the four child IDs in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`;
* declaration names and the notions `I-power`, `power torsion`, `Ext`,
  `neighbourhood`, and `flat map` in all `WeilConjectures/**/*.lean` files.

There is no exact declaration or blueprint tag for the item or any child, and
there is therefore no Lean attachment.  Nothing in that checkout was written
or built.  The current DAG was searched for each child ID and the cited
definitions before accepting the split; no duplicate node was introduced.

### Step-by-step check

1. The chosen presentation is the first construction in 05E8
   (`more-algebra.tex`, label `lemma-I-power-torsion-presentation`, lines
   24002--24019).  Each element of the direct sum has finite support, so a
   common maximum of the finitely many annihilating powers kills it; hence the
   kernel is again `I`-power torsion.  Flatness and right exactness give the
   displayed exact base-changed sequence.  The cited presentation, flat-tensor,
   right-tensor, and base-change nodes state exactly these facts; the finite
   support observation is elementary.

2. The pullback `T` is defined explicitly and its exactness follows by the
   kernel and surjectivity checks written in the step.  Restricting to each
   summand gives an extension of `(R/I^n)_S`; the cyclic child is exactly the
   05EG reduction to `R/I^n` (lines 24519--24526, with the explicit cyclic
   Ext calculation at lines 24529--24555).  The direct-sum child records the
   omitted Ext/direct-sum assembly in 05EG and supplies an extension of `P`.
   The exact-sequence and module-base-change citations provide only the stated
   transport of end maps.  The pullback verification itself is elementary.

3. The map `t_S(z) = (0,k_S z)` is well-defined because `p_S k_S = 0`.
   Hom comparison is the part (2) of 05EC (label
   `lemma-neighbourhood-equivalence`, lines 24301--24333): its source `K` is
   torsion, so it gives existence and uniqueness of `s`, and applying the same
   injectivity to target `P` proves `b s = k`.  Since `k` is injective, `s` is
   injective; the image-intersection argument with `a` is a direct diagram
   chase.  No uncited non-elementary fact is used.

4. The quotient `E_P/s(K)` is introduced with the quotient-module definition.
   The intersection result from step 3 proves that `j` is injective.  The map
   `p b` kills `s(K)` and is surjective, and the kernel computation uses only
   the two exact sequences and the explicitly chosen preimage in `K`.  Thus the
   exactness assertion is a direct elementwise check from the cited nodes.

5. Tensoring `K -> E_P -> E -> 0` with the flat `S` identifies `E_S` with the
   quotient by `s_S(K_S)`.  Under `alpha`, that submodule is exactly the kernel
   of `pr_1 : T -> M'`: if the first coordinate is zero, the second lies in
   `ker p_S = im k_S`, and the converse is immediate.  The induced map is
   therefore the required `theta`; the two commutative identities are checked
   in the final displayed equalities.  All non-elementary tensor facts are
   cited, and the quotient/kernel argument is elementary.

### New child nodes (B1--B7 and C5)

* `lem-weil-pbc-torsion-cyclic-presentation` is statement-only and
  self-contained: it introduces `R`, `I`, `Q`, the index set, powers, direct
  sum, map, and torsion kernel.  Its source is the Stacks tag 05E8 (not a
  section number).  No Mathlib declaration is an exact match; the worker's
  LeanSearch, LeanFinder, and grep searches are recorded in the node.
* `lem-weil-pbc-torsion-hom-flat-comparison` introduces all rings, ideal,
  modules, torsion condition, and the natural Hom map.  It is the precise
  torsion-source clause of 05EC (lines 24301--24333), with no proof material in
  the statement.  The recorded Mathlib searches found no match.
* `lem-weil-pbc-cyclic-extension-flat-descent` introduces the map, ideal,
  exponent, module, cyclic quotient, base change, and complete short exact
  sequence.  It states the cyclic specialization supplied by 05EG's reduction
  and explicit calculation; the source tag and lines are recorded, and the
  Mathlib searches found no match.
* `lem-weil-pbc-direct-sum-extension-assembly` introduces the flat map, target
  module, arbitrary family, direct sum, and the per-summand descent hypothesis,
  then states the assembled extension.  It is the direct-sum compatibility
  detail that 05EG explicitly leaves omitted at lines 24520--24526.  The
  arbitrary index set is deliberate, since the 05E8 presentation need not be
  finite.  No Mathlib exact match was found.

All four children have `blueprint = {is, from, same_as}`.  Their `from` fields
point to the nearest blueprint ancestor and the exact essential-surjectivity
place used by this proof, and `same_as` is empty after the whole-blueprint
search.  They are unsplit leaves with no proof, proof dependencies, or hidden
definitions.  Their statements use existing definition nodes for flat maps,
base change, exact sequences, direct sums, and quotients.  The source tags and
line ranges are present in every source record.  `review_split.py` passes, and
the DAG check reports zero cycles (only the seven unrelated pre-existing
reachability notices).

### Section E and edge cases

The flatness hypothesis is used exactly in steps 1 and 5 for preservation of
the displayed injections/right-exact quotients, and in step 2 through the
base-changed pullback.  Finite generation of `I` is needed by 05EC/05EG and is
carried by the item and cyclic/Hom children.  Torsion of `Q` is used only to
obtain the cyclic presentation and torsion kernel; torsion of `K` is then used
in step 3.  The quotient construction was tested on `Q = 0`, on one summand
`Q = R/I^n`, and on an infinite direct sum: the maps reduce respectively to
the zero extension, the cyclic child, and the arbitrary-family assembly, with
no change in the argument.  For `I = 0`, the torsion condition forces `Q = 0`
because the convention is a positive power, and the same zero-extension check
still applies.

### Feedback and changes

I found no statement or citation defect to send back.  The worker's split and
metadata were retained unchanged; this report supplies the required lead
review and records the new slopmaster2 source audit.  No delivery push was
performed from this review worktree.
