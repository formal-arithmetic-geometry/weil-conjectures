# Worker report: lem-kun-kunneth-map-agrees

1. **Files written.** \`dag/nodes/sec-smooth-purity/lem-kun-kunneth-map-agrees.json\` is the only node file changed. \`citations.json\` was refreshed for all twelve steps. No new DAG nodes are created; the three temporary nodes from the returned version were deleted because their content is already stated by existing nodes. No Lean file, compiler, Lake, or build command was run.

2. **Attachments.** None. I searched the project source for the item tag and canonical Kunneth agreement declarations; no sorry-free declaration states this item exactly.

3. **WANTED:** Local copies of the Stacks source files for Tags 0F14, 0F0E, 0F0F, 0F0C, 0F0G, 0F10, 0F12, 0B56, 07A4, 0D6E, 0037, and 0DV0. The proof follows the current blueprint and the statements of the cited DAG nodes, with source locators retained in the proof steps.

4. **Returned faults repaired.**

   - Removed \`lem-kun-composition-adjunction-normalization\`: its inverse-image order was wrong, it contained a proof sketch despite being statement-only, and its content duplicates \`lem-sfb-derived-composition-adjunction-normalization\`, the module-composition node's final clause, and the normalized ringed-topoi composition node.
   - Removed \`lem-kun-separably-closed-derived-adjunction\`: its objects were under-specified and its compatibility clauses were not equalities. Step 2 now derives the needed identifications directly from \`def-kun-rgamma-unbounded\`, \`lem-kun-pullback-constant\`, \`def-kun-constant-projection-morphism\`, and the existing point-equivalence nodes.
   - Removed \`lem-kun-separably-closed-module-evaluation\`: its opening repeated \`lem-kun-0ezp\`, and the module-equivalence content is already covered by \`lem-kun-geometric-point-derived-constants\`, \`lem-exc-abelian-sheaves-gmodules\`, and \`lem-exc-field-discrete-modules\`. The integer and finite-coefficient cases are now stated separately in step 1.
   - Corrected every internal reference after the twelve-step expansion: step 5 now points to steps 2 and 4; step 6 points to steps 5 and 3; step 7 points to step 5 and step 3; and step 12 uses invertibility from steps 8–11, identifies the Kunneth map in step 7, and cites tensor descent from step 4.
   - The item proof sources now point to actual sentences in the current blueprint proof rather than invented paragraph names. No new node has a blueprint source or duplicate-search obligation.

5. **Unfinished work.** None at stage 1.

## Review by Q80

I reread the current \`main-20261015\` blueprint proof, the item statement and dependencies, the return entry, and the complete statements of every node cited by all twelve steps. The item statement remains unchanged: case (a) has the qcqs hypothesis on \(Y\), case (b) has finite type over the separably closed field and \(n\) invertible, the coefficient categories are exactly Λ=ℤ and Λ=ℤ/nℤ, and the displayed maps \(e,t,r,\ell,\theta\) have the stated source and target.

- **Steps 1–2.** \`lem-kun-0ezp\` supplies the disjoint-union description. For Λ=ℤ, \`lem-kun-geometric-point-derived-constants\` supplies the exact derived constant/stalk equivalence and its tensor normalization. For Λ=ℤ/nℤ, \`lem-exc-abelian-sheaves-gmodules\` and \`lem-exc-field-discrete-modules\` specialize to the trivial Galois group and identify finite-Λ module sheaves with modules, with sections as invariants. \`def-kun-rgamma-unbounded\` and \`lem-kun-pullback-constant\` give \(A,B,\underline A\); \`def-kun-constant-projection-morphism\` and \`def-kun-derived-tensor\` identify the resulting counit and tensor comparison with \(r\). I checked that no undefined \(E,K,R_f,R_g,L_g\) remain in a node statement.

- **Step 3.** \`lem-weil-pbc-ringed-topoi-derived-pushforward-composition\` gives the canonical Leray comparison and its K-injective normalization. \`lem-sfb-derived-composition-adjunction-normalization\` states that this normalized comparison is the conjugate of the composite derived adjunction. \`def-weil-pbc-composite-adjunction\` supplies the composite unit/counit convention, and the final clause of \`lem-weil-pbc-inverse-image-composition-module-linear\` identifies the module composition map carrying the composite unit to the single-map unit. Thus the step uses exactly what each cited statement says.

- **Step 4.** I reread the inverse-image monoidal, derived tensor, K-flat descent, tensor symmetry, exact module pullback, K-flat pullback, and module-composition statements. The local pure-tensor, differential, and sign checks are a single explicit coherence argument; the descent node promotes them to arbitrary derived objects.

- **Steps 5–7.** I checked the definitions of the constant projection, unbounded exchange, projection-formula map, composite adjunction, Kunneth map, and the adjunct/counit identity. Step 5 computes the three counit identities and uses the symmetry check from step 4. Step 6 forms \(m,v,\lambda\) and computes its composite-adjunction transpose using the normalization from step 3. Step 7 substitutes the projection and exchange identities from step 5 and compares the resulting typed adjoint with the exact α in \`def-kun-kunneth-map\`; injectivity of the same Hom bijection gives λ=κ.

- **Steps 8–10.** Properness is stable under the fibre product; exact inverse image preserves lower bounds; \`lem-weil-pbc-inverse-image-torsion\` supplies torsion cohomology. The bounded projection and proper-base-change theorems apply, and \`lem-kun-unbounded-exchange-agrees\` verifies that the bounded map is the same unbounded exchange. Enough injectives, the bounded-below representative, and the bounded/unbounded global-sections comparison put \(A\) in the required \(D^+\) category; qcqs \(Y\) then makes \(r\) invertible. The ringed-topoi comparison makes \(\ell\) invertible.

- **Step 11.** I checked \(n1_\Lambda=0\), properness, finite type over the Noetherian point, local Noetherianity, quasi-separatedness, and finite cohomological dimension before applying \`lem-kun-0f0g\`, \`lem-kun-0f0c\`, and \`lem-kun-0f12\`. No boundedness or finite Tor-amplitude assumption is added.

- **Step 12.** I reread the factorization from steps 5–7 and the signed symmetry. The inverse factors are all supplied by steps 8–11; the two symmetry maps square to the identity, so the displayed θ is the inverse of λ=κ and θ∘κ is the identity.

I searched the whole DAG and current blueprint for each proposed temporary node before deleting it. Existing same-unit nodes cover the point equivalence and composition normalization, so no duplicate node remains. Every \`uses\` id exists and is unmerged, \`proof_deps\` is exactly their union, and every entry in \`citations.json\` is a verbatim substring of the cited statement.
