# Section 5 — Paper Packet

## Lemma 5.1

- paper_id: Lemma 5.1
- object_type: lemma
- section: 5
- source_pages: [222, 223, 224]
- exact_statement_or_close_paraphrase: Suppose $u_0, u_1$ are complex numbers such that $|u_0| = |u_1| = 1$. There exist 2-qubit unitaries $U_1, U_2, U_3, U_4$ such that $U_1^{BC} U_2^{AC} U_3^{AB} U_4^{BC} = CC(\mathrm{Diag}(u_0, u_1))$ if and only if either $u_0 = u_1$ or $u_0 u_1 = 1$.
- paper_dependencies_explicit: [Lemma 3.1, Lemma 4.1, Lemma A.24]
- paper_dependencies_implicit: [properties of CC and Diag constructions, commutativity of diagonal matrices, tensor product structure of BC-type gates]
- proof_sketch_summary: Left-to-right: Rearrange to isolate $U_2^{AC} U_3^{AB}$ and observe that $U_1^{BC\dagger}$, $CC(\mathrm{Diag}(u_0, u_1))$, and $U_4^{BC\dagger}$ each commute with $\mathrm{Diag}(u_0, u_1) \otimes I_{BC}$. Apply Lemma 3.1 to get either $u_0 = u_1$ (done) or $U_2^{AC} U_3^{AB} = |0\rangle\langle 0| \otimes V_0^{BC} + |1\rangle\langle 1| \otimes V_1^{BC}$. Apply Lemma A.24 to refine this into a tensor product form $|0\rangle\langle 0| \otimes P_0 \otimes Q_0 + |1\rangle\langle 1| \otimes P_1 \otimes Q_1$. Substitute back and apply Lemma 4.1 to conclude $u_0 = u_1$ or $u_0 u_1 = 1$. Right-to-left: Case $u_0 = u_1$: set $U = C(\mathrm{Diag}(1, u))$ and verify $I^{BC} I^{AC} U^{AB} I^{BC} = CC(\mathrm{Diag}(u, u))$ directly. Case $u_0 u_1 = 1$: define explicit matrices $U$, $V = \mathrm{Diag}(1,1,1,u_1)$, $W = \mathrm{Diag}(1,1,1,u_0)$ and verify $U^{BC} V^{AC} V^{AB} U^{BC} = CC(\mathrm{Diag}(u_0, u_1))$ by direct calculation.
- extraction_confidence: high
- ambiguities: Lemma A.24 is from the appendix; its precise statement was not re-verified here but is cited explicitly in the proof.
