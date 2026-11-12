import A084029Table

open A084029

set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
/-- Certificat partiel (bas) de la table `table029` : pour chaque
    n ∈ [3,65], la liste `table029 n` a n éléments distincts,
    chacun multiple de n à n chiffres de somme n.
    Même énoncé et même preuve que `table029_ok_all`
    (A084029.lean), restreint à la moitié basse de la plage ;
    le `decide +kernel` est refait par interval_cases sur ce
    sous-intervalle. -/
theorem cert_lo :
    ∀ n ∈ Finset.Icc 3 65,
      n ≤ (table029 n).length ∧ (table029 n).Nodup ∧
        ∀ N ∈ table029 n,
          n ∣ N ∧ (Nat.digits 10 N).length = n ∧
            (Nat.digits 10 N).sum = n := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h3, h65⟩ := hn
  interval_cases n <;> decide +kernel
